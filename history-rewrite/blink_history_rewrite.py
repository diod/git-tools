#!/usr/bin/env python
# -*- coding: utf-8 -*-
# -*- mode:python -*-
# Copyright (c) 2014 Primiano Tucci -- www.primianotucci.com
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#
# * Redistributions of source code must retain the above copyright notice, this
#   list of conditions and the following disclaimer.
# * Redistributions in binary form must reproduce the above copyright notice,
#   this list of conditions and the following disclaimer in the documentation
#   and/or other materials provided with the distribution.
# * The name of Primiano Tucci may not be used to endorse or promote products
#   derived from this software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
# AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
# IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
# DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT OWNER OR CONTRIBUTORS BE LIABLE
# FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
# SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
# CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
# OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
# OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

"""Rewrite the history of Blink, moving large files out of the repo.

For each binary file (png, mp3, ...) under /LayoutTests:
 - The file is copied to DIRS.GCS/sha1.blob, where sha1 == Git SHA1 for the blob
   (i.e. files in the GCS have the same SHA1 of the blobs in the original repo).
 - The file.png is removed from the tree.
 - A new blob, named orig_filename.png.gitcs, is inserted in the tree. This
   file contains a ref to the final GCS bucket (gs://blink-gitcs/sha1.blob).

Furthermore, the /LayoutTests/.gitignore file is changed (or created) in order
to add ignore the _BIN_EXTS below.
"""

from __future__ import print_function

import multiprocessing
import os
import subprocess
import sys
import time
import traceback
import logging
import sys
import random
import types
import re

from array import array
from collections import OrderedDict


sys.path.append(os.path.abspath(os.path.dirname(__file__)))
from gitutils import *


_SKIP_COPY_INTO_CGS = True

_BIN_EXTS = ({'.aif', '.bin', '.bmp', '.cur', '.gif', '.icm', '.ico', '.jpeg',
              '.jpg', '.m4a', '.m4v', '.mov', '.mp3', '.mp4', '.mpg', '.oga',
              '.ogg', '.ogv', '.otf', '.pdf', '.png', '.sitx', '.swf', '.tiff',
              '.ttf', '.wav', '.webm', '.webp', '.woff', '.woff2', '.zip', 
              '.eot', '.marisa', '.xls', '.xlsx', '.psd'})

_KILL_EXTS = ({'.msi'})

class DIRS:
  # The .git/objects dir containing the original loose objects.
  ORIGOBJS = '/mnt/d_scratch/loose'  # Will be figured out at runtime using git --git-dir.

  # Where the new git objects (trees, blobs) will be put.
  NEWOBJS = '/mnt/d_scratch/tmp'

  # Where the binary files (then uploaded to GCS) will be moved.
  GCS = '/mnt/d_scratch/gcs-bucket/'


# _tree_cache is a map of tree-ish -> translated tree-ish and is used to avoid
# re-translating sub-trees which are identical between subsequent commits
_tree_cache = multiprocessing.Manager().dict()

# collected - trees already seen by _CollectTree
_collected_tree = multiprocessing.Manager().dict()

# A map of <original tree SHA1 (hex)> -> <translated SHA1> for top-level trees.
# Contains the results of _TranslateOneTree calls.
_root_trees = multiprocessing.Manager().dict()

# map for patched files
_file_cache = multiprocessing.Manager().dict()

# set of SHA1s (just to keep the total count)
_gcs_blobs = multiprocessing.Manager().dict()

_local_file_cache = {}
_local_collected_cache = {}
_local_tree_cache = {}

mt_tree = OrderedDict({});

log = None

def _BuildGitignoreMaybeCached(base_sha1=None):
  cache_key = base_sha1.raw if base_sha1 else 'blank'
  cached_gitignore = _tree_cache.get(cache_key)
  if cached_gitignore:
    return SHA1(cached_gitignore)
  else:
    gitignore = ''
    if base_sha1:
      gitignore = ReadGitObj(base_sha1, DIRS.ORIGOBJS)[2] + '\n'
    gitignore += '\n'.join(('*' + x for x in sorted(_BIN_EXTS))) + '\n'
    sha1 = WriteGitObj('blob', gitignore, DIRS.NEWOBJS)
    collision = _tree_cache.setdefault(cache_key, sha1.raw)
    assert(collision == sha1.raw)
    return sha1


def _GuessGitFileEnc( sha1, buf, log ):

    ln = len(buf);

    if ln<3:
      return 'TOOSHORT %d' % ln;
    
    if (buf[0] == '\xEF') and (buf[1] == '\xBB') and (buf[2] == '\xBF'):
      return 'UTFBOM';
      
    xml = b'<?xml version="1.0" encoding="utf-8"';
    if (buf[0:len(xml)] == xml):
      return 'UTFXML';

    xml = b'<?xml version="1.0" encoding="UTF-8"';
    if (buf[0:len(xml)] == xml):
      return 'UTFXML';
      
    xml = b'<?xml version="1.0" encoding="windows-1251"';
    winxml = False
    if (buf[0:len(xml)] == xml):
      winxml = True ;
     
    # histo 
    readlen = min(8192, ln);  #to analyze
      
    histo = array('I', [0] * 256)
    for i in range(0, readlen):
      c = ord(buf[i]);
      histo[ c ] = histo[ c ] + 1;
    
    total8bit = 0
    for i in range(128,256):
      total8bit = total8bit + histo[i];
     
    if (total8bit == 0):
      return 'ASCII';
      
    if (total8bit == (histo[0xA0] + histo[0x93] + histo[0x94])) and not winxml:
      return 'WINDET';
      
    d0d1 = histo[ 0xD0 ] + histo[ 0xD1 ];
    utfd = float(d0d1) / float( total8bit - d0d1);
    if (d0d1 > 0) and ( utfd > 0.9) and not winxml:
      return 'UTFDET'; 
     
    c0ff = 0
    for i in range(0xC0, 0xFF+1):
      c0ff = c0ff + histo[i];

    c0ff = c0ff + histo[0xA0] + histo[0x93] + histo[0x94];
      
    dgtsnsyn = 0
    for i in range(32,64+1):
      dgtsnsyn = dgtsnsyn + histo[i];
    for i in range(91,96+1):
      dgtsnsyn = dgtsnsyn + histo[i];
    for i in range(123,126+1):
      dgtsnsyn = dgtsnsyn + histo[i];

    win = float(c0ff)/float(total8bit);
    if ((win > 0.95) or winxml) and (histo[0x98] == 0):
      return 'WINDET';

    print('Histo:', file=log);
    for i in range(0,256):
      if (histo[i] > 0):
        print("  %02x %3d %ld" % (i, i, histo[i]), file=log);
      
    print("%s: len: %ld, t8b: %ld, d0d1: %ld, d0d1r: %0.2f, c0ff: %d, dgtsnsyn: %d, win: %0.2f winxml: %d, histo[98]: %d" % (sha1.hex, ln, total8bit, d0d1, utfd, c0ff, dgtsnsyn, win, winxml, histo[0x98]), file=log );
      
    return 'UNK';



def _DumpTree(indent, tree, log):
    for _fname in tree:
      (_mode, _, _sha1, _children) = tree[_fname]
      if _sha1 is None:
        _h = 'None'
      else:
        _h = _sha1.hex

      print("%s  %s %s %s %d" % ( indent, _mode, _fname, _h, len(_children)), file=log);

      if len(_children):
        _DumpTree( indent + '>', _children, log);



def _TreeAddDir(tree, dirname, log, path='', sha1 = None):
  if dirname in tree:
    if (sha1 is None):
      return;
    elif not (tree[dirname][2] is None) and ((tree[dirname][2]).hex == sha1.hex):
      return;
    elif not (tree[dirname][2] is None) and ((path == '/ruscorpora/trunk/corpora/slav/mid_rus_new') or (path == '/ruscorpora/trunk/corpora/slav/mid_rus_new/texts')):
      print("ERR: re-adding tree item %s with sha[forced]: %s (original sha: %s), path=%s" % ( dirname, sha1.hex, (tree[dirname][2]).hex, path), file=log);
    elif not (tree[dirname][2] is None):
      print("ERR: not re-adding tree item %s with sha: %s (original sha: %s), path=%s" % ( dirname, sha1.hex, (tree[dirname][2]).hex, path), file=log);
      return;
    elif ((path == '/ruscorpora/trunk/corpora/slav/mid_rus_new') or (path == '/ruscorpora/trunk/corpora/slav/mid_rus_new/texts')):
      print("ERR: re-adding tree item %s with sha: %s (original sha is None), path=%s" % ( dirname, sha1.hex, path ), file=log);
    else:
      print("ERR: not re-adding tree item %s with sha: %s (original sha is None), path=%s" % ( dirname, sha1.hex, path ), file=log);
      return
    

  mode = '40000'

  tree[dirname] = ( mode, dirname, sha1, OrderedDict({}) );



def _TreeAppend(tree, mode, file, sha1, log, path):
  if file in tree:
    if not (tree[file][2] is None) and ((tree[file][2]).hex == sha1.hex):
      return;
    else:
      print("ERR: re-adding tree item %s:%s:%s (original sha: %s), path=%s" % ( file,mode,sha1.hex, tree[file][2].hex, path), file=log )
 
  tree[file] = ( mode, file, sha1, OrderedDict({}) )



def _MaterializeTree(tree, target, path, log):
  
  entries = OrderedDict({})
  for fname in sorted(tree):
    _mode, _fname, _sha1, _children = tree[fname]
    if (_sha1 is None):
      if len(_children) > 0:
        _sha1 = _MaterializeTree(_children, target, path + '/' + _fname, log);
      else:
        print("MATERR: empty children+sha1 for %s/%s" % (path, _fname), file=log);
    else:
      if len(_children) > 0:
        print("MATERR: contents in children+sha1 for %s/%s" % (path, _fname), file=log);

    _TreeAppend( entries, _mode, _fname, _sha1, log, path )

  log.flush();
  
  res = WriteGitTree(entries.values(), target)
  return res;



def _RootMaterializeTree(tree, target, path, log):
  split_trees = OrderedDict({})

  for fname in sorted(tree):
    _mode, _fname, _sha1, _children = tree[fname]
    if (_sha1 is None):
      if len(_children) > 0:
        _sha1 = _MaterializeTree(_children, target + '/' + _fname, path + '/' + _fname, log);
      else:
        print("MATROOTERR: empty children+sha1 for %s/%s" % (path, _fname), file=log);
    else:
      if len(_children) > 0:
        print("MATROOTERR: contents in children+sha1 for %s/%s" % (path, _fname), file=log);
      else:
        continue;

    split_trees[_fname] = _sha1;

  log.flush();

  return split_trees;



MAP_UNKNOWN=('godeepr','');
MAP_DROP=('drop','');

def _TreePathMapping(indent, fname, path, log):

  if (indent == 0):
    if (fname == 'ruscorpora'):
      return MAP_UNKNOWN;
    else:
      print("ERR: unknown L0 branch: %s/%s drop" % (path, fname), file=log);
      return MAP_DROP;
      
  if (indent == 1):
    if (fname == 'trunk'):
      return MAP_UNKNOWN;
    if (fname == 'branches'):
      return MAP_DROP
    
  if (indent == 2):
    if (fname == 'corpora'): #lexicografically first
      return MAP_UNKNOWN;

    elif (fname == 'www') or (fname == 'saas') or (fname == 'conf') or (fname == 'db') or (fname == 'hooks') or (fname == 'locks') or (fname == 'ruscorpora_suggest') or (fname == 'makeup') or (fname == 'tagged'):
      return MAP_DROP;

    elif (fname == 'README.txt') or (fname == 'format'):
      return MAP_DROP;

    elif (fname == 'accent'):
      return ('accent', 'accent_main/texts');
      
    elif (fname == 'spoken') or (fname == 'tables'):
      return (fname, '')
    
    elif (fname == 'research'):
      return ('projects', '')
      
    elif (fname == 'standard') or (fname == 'source'):
      return ('main', '')

    elif (fname == 'texts'):
      return MAP_UNKNOWN;
    

  _parent = os.path.split(path);
  parent = _parent[1];
  parentparent = os.path.split(_parent[0])[1];

  if (indent == 3):
    if (parent == 'corpora'):

      if (fname == 'spoken'):
        return MAP_UNKNOWN
      if (fname == 'version'):
        return MAP_DROP
      if (fname == 'para_rus_ger'):
        return MAP_DROP
      if (fname == '18century') or (fname == 'folklore') or (fname == 'test_corpus') or (fname == 'research'):
        return ('projects', '');
      if (fname == 'slav'):
        return MAP_UNKNOWN
      else:
        return (fname, '')  #... ,tables

    if (parent == 'spoken'):
      
      if (fname == 'manual'):
        return (parent, 'manual/texts')
      elif (fname == 'private') or (fname == 'public'):
        return (parent, 'texts/%s' % fname)
      elif (fname == 'tabl_manual_spoken.csv'):
        return (parent, 'manual/tables', 'manual.csv')
      elif (fname == 'spoken.csv'):
        return (parent, 'tables')
      elif (fname == 'murco'):
        return ('murco', '/');

    if (parent == 'standard') or (parent == 'source'):
      
      if (fname == 'pre1950') or (fname == 'post1950'):
        return ('main', '%s/texts/%s' % (parent, fname))
      elif (fname == 'standard_1.csv'):
        return ('main', '%s/tables' % parent, 'standard.csv');
      
    if (parent == 'texts'):
      
      if (fname == 'source') or (fname == 'standard'):
        return ('main', '%s/texts' % fname);
      elif (fname == 'accent'):
        return ('accent', '')
      elif (fname == 'school') or (fname == 'syntax'):
        return (fname, 'texts')
      elif (fname == 'dialect') or (fname == 'spoken') or (fname == 'murco') or (fname == 'poetic') or (fname == 'para') or (fname == 'paper'):
        return (fname, '')

    if (parent == 'research'):
      return ('projects', '%s/%s' % (parent, fname));

    if (parent == 'tables'):
      return (parent, '/');


  if (indent == 4):
    if (parent == 'dialect'):
      if (fname == 'texts') or (fname == 'tables'):
        return (parent, fname)
      elif (fname == 'dialect.csv'):
        return (parent, 'tables')
  
    if (parent == 'spoken'):

      if (fname == 'private') or (fname == 'public'):
        return (parent, 'texts/%s' % fname)
      elif (fname == 'tabl_manual_spoken.csv'):
        return (parent, 'manual/tables', 'manual.csv')
      elif (fname == 'spoken.csv'):
        return (parent, 'tables')
      elif (fname == 'tables') or (fname == 'texts') or (fname == 'manual') or (fname == 'murco') or (fname == 'accent'):
        return (parent, '')

    if (parent == 'murco'):
      if (fname == 'kino'):
        return (parent, '');
      if (fname == 'private') or (fname == 'public'):
        return (parent, 'texts/%s' % fname )
      elif (fname == 'murco.csv') or (fname == 'video_ids.txt'):
        return (parent, 'tables');
      elif (fname == 'texts') or (fname == 'tables') or (fname == 'meta'):
        return (parent, fname)    
  
    if (parent == 'poetic'):
      if (fname == 'xix') or (fname == 'xviii') or (fname == 'xx'):
        return (parent, 'texts/%s' % fname );
      elif (fname == 'poetic.csv'):
        return (parent, 'tables');
      elif (fname == 'texts'):
        return (parent, '')    
      elif (fname == 'tables'):
        return (parent, fname);
      
    if (parent == 'main'):
      if (fname == 'source') or (fname == 'standard'):
        return (parent, fname)
  
    if (parent == 'para'):
      if (fname == 'texts') or (fname == 'tables'):
        return (parent, '')
      if (fname == 'para.csv'):
        return (parent, 'tables');
      if (fname[0:3] == 'rus') or (fname[-3:] == 'rus'):
        return (parent, 'texts/%s' % fname )  
  
  
    if (parent == 'accent'):
      if (fname == 'texts') or (fname == 'tables'):
        return (parent, 'accent_main/%s' % fname);
      elif (fname == 'accent.csv'):
        return (parent, 'accent_main/tables');
      elif (fname == 'public') or (fname == 'private') or (fname == 'kino'):
        return (parent, 'accent_main/texts/%s' % fname);
      else:
        return (parent, fname);
  
    if (path == '/ruscorpora/trunk/corpora/tables'):
      if (fname == 'validation'):
        return ('tables', fname);
      else:
        return ('tables', '/');
  
    if (path == '/ruscorpora/trunk/texts/paper'):
      if (fname == 'RIAN'):
        return (parent, 'texts/%s' % fname.lower());
      elif (fname == 'paper.csv'):
        return (parent, 'tables');
      else:
        return (parent, 'texts/%s' % fname);
  
    if (path == '/ruscorpora/trunk/corpora/paper'):
      if (fname == 'README.txt') or (fname =='Desktop.ini') or (fname == 'conf') or (fname == 'db') or (fname == 'format') or (fname == 'hooks') or (fname =='locks') or (fname == 'svn.ico'):
        return MAP_DROP
    
  
    if (parent == 'regional_grodno') or (parent == 'multiparc'):
      if fname[-3:] == 'xls':
        return (parent, '/');
      else:
        return (parent, fname);
      
    if (parent == 'slav'):
      if (fname == 'texts') or (fname == 'tables') or (fname == 'old_slav'):
        return MAP_UNKNOWN
      elif (fname == 'orthlib') or (fname == 'birchbark') or (fname == 'mid_rus') or (fname == 'old_rus'):
        return (fname, '');
      elif (fname == 'mid_rus_new'):
        return ('mid_rus', '');
      elif (fname == 'txt-renamer.py'):
        return MAP_DROP; 
      elif (re.search(r'_akty_.*txt', fname)):
        return ('mid_rus', 'texts/gramoty_akty_14_16');
      elif (fname == 'Летописец начала царства-out.txt'):
        return ('mid_rus', 'texts/letopisets', 'Letopisets-out.txt');
      elif (fname == 'meta.xls'):
        return ('mid_rus', fname);
      else:
        return ('mid_rus', '');
      
    if (parent == 'test_corpus'):
      if (fname == 'README'):
        return ('projects', parent);
      else:
        return ('projects', '%s/%s' % (parent, fname));

    if (parent == '18century'):
      if (fname == 'table') or (fname == 'tables'):
        return ('projects', '%s/tables' % parent);
      elif (fname == 'texts'):
        return ('projects', '%s/%s' % (parent, fname));

    if (parent == 'folklore'):
      return ('projects', '%s/%s' % (parent, fname));

    if (parent == 'research'):
      return ('projects', '%s/%s' % (parent, fname));
  
    # any parent        
    if (fname == 'texts') or (fname == 'tables'):
      return (parent, fname)    
  
  if indent==5:
    if (path == '/ruscorpora/trunk/corpora/para/texts') or (path == '/ruscorpora/trunk/corpora/para/tables'):
      if (fname[0:3] == 'rus') or (fname[-3:] == 'rus') or (fname == 'multi'):
        return ('para', 'texts/%s' % (fname))
      if (fname[-3:] == 'csv'):
        return ('para', 'tables')
      if (fname[-4:] == 'djvu'):
        return ('para', 'tables')
        
    if (path == '/ruscorpora/trunk/corpora/murco/kino') or (path == '/ruscorpora/trunk/texts/murco/kino'):
      return ('murco', 'kino/%s' % fname.lower());
      
    if (path == '/ruscorpora/trunk/corpora/poetic/texts'):
      if (fname == 'poetic'):
        return (fname, '');
      else:
        return ('poetic', 'texts/%s' % fname);
      
    if (path == '/ruscorpora/trunk/corpora/spoken/texts'):
      if (fname == 'manual'):
        return ('spoken', 'manual/texts');
      elif (fname == 'spoken.csv'):
        return ('spoken', 'tables')
      elif (fname == 'tabl_manual_spoken.csv'):
        return ('spoken', 'manual/tables', 'manual.csv');
      else:
        return ('spoken', 'texts/%s' % fname);
      
    if (path == '/ruscorpora/trunk/corpora/spoken/manual') or (path == '/ruscorpora/trunk/texts/spoken/manual'):
      if (fname == 'texts'):
        return ('spoken', 'manual/texts');
      elif (fname == 'tables'):
        return ('spoken', '');
      else:
        return ('spoken', 'manual/texts/%s' % fname);  # ruscorpora/trunk/corpora/spoken/manual/kino/beloe_solnce.acc.xh

    if (path == '/ruscorpora/trunk/corpora/spoken/tables'):
      if (fname == 'tabl_manual_spoken.csv'):
        return ('spoken', 'manual/tables', 'manual.csv');
      elif (fname == 'spoken.csv'):
        return ('spoken', 'tables');
      else:
        return ('spoken', 'tables');

    if (path == '/ruscorpora/trunk/corpora/spoken/murco'):
      return ('murco', fname);
    if (path == '/ruscorpora/trunk/corpora/spoken/accent'):
      return ('accent', fname);

    if (parentparent == 'slav'):
      if (parent == 'mosk_del_byt_pism-1') or (parent == 'pskov_letopisi') or (parent == 'morozov') or (parent == 'jaroslav_etc') or (parent == 'gramoty_akty_14_16') or (parent == 'gramotki_17_18') or (parent == 'duhovnye_dogovornye') or (parent == 'BDRL') or (parent == 'letopisets'):
        return ('mid_rus', 'texts/%s' % parent )
      elif (parent == 'Грамотки 17 - нач. 18 вв'):
        return ('mid_rus', 'texts/gramotki_17_18')
      elif (parent == 'Духовные и договорные грамоты'):
        return ('mid_rus', 'texts/duhovnye_dogovornye')
      elif (parent == 'Моск. дел. и быт. письм. Отд. 1'):
        return ('mid_rus', 'texts/mosk_del_byt_pism-1')


    if (path == '/ruscorpora/trunk/corpora/slav/texts'):
      if (fname == 'orthlib'):
        return ('orthlib', 'texts')
      if (fname == 'old_slav'):
        return ('old_rus', 'texts')
      if (fname == 'melissa') or (fname == 'npl'):
        return ('old_rus', 'texts/%s' % fname )

    if (path == '/ruscorpora/trunk/corpora/slav/tables'):
      if (fname == 'slav.csv') or (fname == 'old_slav.csv'):
        return ('old_rus', 'tables', 'old_rus.csv')
      if (fname == 'orthlib.csv'):
        return ('orthlib', 'tables')

    if (path == '/ruscorpora/trunk/corpora/slav/old_slav'):
      if (fname == 'texts'):
        return MAP_UNKNOWN;
      if (fname == 'tables'):
        return ('old_rus', '');

    if (path == '/ruscorpora/trunk/corpora/slav/old_rus'):
      if (fname == 'texts'):
        return ('old_rus', fname);
      if (fname == 'tables'):
        return ('old_rus', '');
        
    if (path == '/ruscorpora/trunk/corpora/slav/orthlib'):
      if (fname == 'texts') or (fname == 'tables') or (fname == 'textss'):
        return ('orthlib', fname);
        
    if (path == '/ruscorpora/trunk/corpora/slav/birchbark'):
      if (fname == 'texts') or (fname == 'tables'):
        return ('birchbark', fname);

    if (path == '/ruscorpora/trunk/corpora/slav/mid_rus'):
      if (fname == 'mosk_del_byt_pism-1') or (fname == 'pskov_letopisi') or (fname == 'morozov') or (fname == 'jaroslav_etc') or (fname == 'gramoty_akty_14_16') or (fname == 'gramotki_17_18') or (fname == 'duhovnye_dogovornye') or (fname == 'BDRL') or (fname == 'letopisets'):
        return ('mid_rus', 'texts/%s' % fname.lower());
      if (fname == 'texts'):
        return ('mid_rus', '');
      if (fname == 'tables'):
        return ('mid_rus', '');
      
    if (path == '/ruscorpora/trunk/corpora/slav/mid_rus_new'):
      if (fname == 'texts') or (fname == 'tables'):
        return ('mid_rus', '');
      if (fname == 'mosk_del_byt_pism-1') or (fname == 'pskov_letopisi') or (fname == 'morozov') or (fname == 'jaroslav_etc') or (fname == 'gramoty_akty_14_16') or (fname == 'gramotki_17_18') or (fname == 'duhovnye_dogovornye') or (fname == 'BDRL') or (fname == 'letopisets') or (fname == 'polotsk'):
        return ('mid_rus', 'texts/%s' % fname.lower());
      if (fname == 'afz1') or (fname == 'afz2') or (fname == 'afz3') or (fname == 'amg') or (fname == 'apd') or (fname == 'bdrl') or (fname == 'drama') or (fname == 'gvnp') or (fname == 'kungur') or (fname == 'letopisi_varia') or (fname == 'nkl') or (fname == 'pososhkov') or (fname == 'psrl34') or (fname == 'rd') or (fname == 'rib') or (fname == 'st_kn') or (fname == 'statspis') or (fname == 'varia') or (fname == 'varia2') or (fname == 'zagovor') or (fname == 'lebedev'):
        return ('mid_rus', 'texts/%s' % fname.lower());
      if (fname == 'GramEval2020-17cent-test.RNC.nolemma.xml'):
        return MAP_DROP 
      
  if (indent==6):
    if (path == '/ruscorpora/trunk/corpora/poetic/texts/poetic'):
      if (fname == 'poetic.csv'):
        return ('poetic', 'tables');
      else:
        return ('poetic', 'texts/%s' % fname);

    if (path == '/ruscorpora/trunk/corpora/spoken/manual/tables'):
      if (fname == 'spoken_manual.csv'):
        return ('spoken', 'manual/tables', 'manual.csv');
      else:
        return ('spoken', 'manual/tables');

    if (path == '/ruscorpora/trunk/corpora/slav/old_slav/tables') or (path == '/ruscorpora/trunk/corpora/slav/old_rus/tables'):
      if (fname == 'old_slav.csv') or (fname == 'old_rus.csv'):
        return ('old_rus', 'tables', 'old_rus.csv');
      
    if (path == '/ruscorpora/trunk/corpora/slav/old_slav/texts'):
      if (fname == 'birchbark'):
        return ('birchbark', 'texts');
      else:
        return ('old_rus', 'texts/%s' % fname);
        
      if (fname == 'npl') or (fname == 'melissa') or (fname == 'nikola') or (fname == 'galician') or (fname == 'volhynian'):
        return ('old_rus', 'texts/%s' % (fname));
        
    if (path == '/ruscorpora/trunk/corpora/slav/mid_rus/texts'):
      if (fname[-3:] == 'xml'):
        return ('mid_rus', 'texts/varia2');
      else:
        return ('mid_rus', 'texts/%s' % fname.lower()); #fix BDRL

    if (path == '/ruscorpora/trunk/corpora/slav/mid_rus/tables'):
      if (fname == 'meta.csv') or (fname == 'mid_rus.csv'):
        return ('mid_rus', 'tables', 'mid_rus.csv');

    if (path == '/ruscorpora/trunk/corpora/slav/mid_rus_new/texts'):
      if (fname == 'mosk_del_byt_pism-1') or (fname == 'pskov_letopisi') or (fname == 'morozov') or (fname == 'jaroslav_etc') or (fname == 'gramoty_akty_14_16') or (fname == 'gramotki_17_18') or (fname == 'duhovnye_dogovornye') or (fname == 'BDRL') or (fname == 'letopisets') or (fname == 'polotsk'):
        return ('mid_rus', 'texts/%s' % fname.lower());
      if (fname == 'afz1') or (fname == 'afz2') or (fname == 'afz3') or (fname == 'amg') or (fname == 'apd') or (fname == 'bdrl') or (fname == 'drama') or (fname == 'gvnp') or (fname == 'kungur') or (fname == 'letopisi_varia') or (fname == 'nkl') or (fname == 'pososhkov') or (fname == 'psrl34') or (fname == 'rd') or (fname == 'rib') or (fname == 'st_kn') or (fname == 'statspis') or (fname == 'varia') or (fname == 'varia2') or (fname == 'zagovor') or (fname == 'lebedev'):
        return ('mid_rus', 'texts/%s' % fname.lower());

    if (path == '/ruscorpora/trunk/corpora/slav/mid_rus_new/tables'):
      if (fname == 'mid_rus_new.csv'):
        return ('mid_rus', 'tables', 'mid_rus.csv');
        
        

  print("ERR: FIXME unprocessed L%d entry %s/%s" % (indent, path, fname), file=log);
  return MAP_DROP
  


def _LookupFile(_trgt, sha1, mode, fname, _fname, log):
  #FIXME: lookup fixed file sha here
  key = _trgt[-4:] + sha1.hex

  if key in _local_file_cache:
    cached_file = _local_file_cache[key]
  else:
    cached_file = _file_cache.get(key)

  if cached_file:
    _local_file_cache[key] = cached_file
    return SHA1(cached_file)
  else:
    otype, ln, payload = ReadGitObj(sha1, DIRS.ORIGOBJS)
    new_file_sha1 = WriteGitObj(otype, payload, DIRS.NEWOBJS + '/' + _trgt);

    print("not-translated: %s %s->%s %s <fixed>" % (mode, fname, _fname, sha1.hex), file=log);
    return sha1

  
  

def _MangleTree(root_sha1, target, log, indent, path, justmount):
  assert(isinstance(root_sha1, SHA1))
  changed = False
  entries = OrderedDict({})

  treekey = target[-4:] + root_sha1.raw

  if treekey in _local_tree_cache:
    cached_translation = _local_tree_cache[treekey]
  else:
    cached_translation = _tree_cache.get(treekey)
  
  if cached_translation and (indent > 5):
    _local_tree_cache[treekey] = cached_translation
    return SHA1(cached_translation)

  if indent < 7:
    print('\n_mangle_tree_sha[%d]: %s trgt:%s' % (indent, root_sha1.hex, target), file=log)


  replace_self_sha1 = None
  base_gitignore_sha1 = None

  _xtree = ReadGitTree(root_sha1, DIRS.ORIGOBJS, target)
  for mode, fname, sha1 in _xtree:
    old_sha1_raw = sha1.raw

    if (indent <= 6) and (justmount == 0):
      resmap = _TreePathMapping(indent, fname, path, log)
    else:
      resmap = ('unk','')
      
    print('>  %d %s %s %s/%s :%d => %s:%s' % ( indent, mode, sha1.hex, path, fname, justmount, resmap[0], resmap[1]), file=log);


    if resmap[0] == 'godeepr':
      replace_self_sha1 = _MangleTree(sha1, target, log, indent+1, '%s/%s' % (path, fname), justmount)
      continue;

    elif resmap[0] == 'drop':
      continue;
     
    elif resmap[0] == 'unk':

      #default processing
      if mode[0] == '1':  # It's a file
        _, ext = os.path.splitext(fname)
      
        key = target[-4:] + sha1.hex
      
        if fname == '.gitignore':
          _TreeAppend( entries, mode, fname, sha1, log, path );
          if _file_cache.get( key ) is None:
            _file_cache.setdefault( key, sha1.raw );

            otype, olen, payload = ReadGitObj(sha1, DIRS.ORIGOBJS, target);
            new_sha1 = WriteGitObj(otype, payload, target)
            assert( sha1.raw == new_sha1.raw )
            
          continue;
      
        elif ext.lower() in _KILL_EXTS:
          # skip adding
          changed = True
          continue;
          
        elif ext.lower() in _BIN_EXTS:
          # add as-is
          _TreeAppend( entries, mode, fname, sha1, log, path );
          if _file_cache.get( key ) is None:
            _file_cache.setdefault( key, sha1.raw );

            otype, olen, payload = ReadGitObj(sha1, DIRS.ORIGOBJS, target);
            new_sha1 = WriteGitObj(otype, payload, target)
            assert( sha1.raw == new_sha1.raw )

          continue;

        else:
          if key in _local_file_cache:
            cached_file = _local_file_cache[key]
          else:
            cached_file = _file_cache.get(key)

          if cached_file:
            _local_file_cache[key] = cached_file
          
          
          _fname = fname
          if (fname[-6:] == '.xhtml'):
            changed = True
            _fname = fname[:-6] + '.xml';
          elif (fname[-7:] == '.xhtml3'):
            changed = True
            _fname = fname[:-7] + '.xml';
          elif (fname[-2:] == '.!'):
            changed = True
            continue;
            
          if (cached_file):
            _TreeAppend( entries, mode, _fname, SHA1(cached_file), log, path );
            changed = changed or (sha1.raw != cached_file)
            continue;
      
          #sha1 = SHA1( _ConvertFile( sha1, target, log ) );
          print("not-translated: i%d t:%s m:%s %s->%s %s in %s" % (indent, target, mode, fname, _fname, sha1.hex, path), file=log);

          _TreeAppend( entries, mode, _fname, sha1, log, path );
          continue;

      else:	#dir
        sha1 = _MangleTree(sha1, target, log, indent+1, '%s/%s' % (path, fname), justmount)
        _TreeAppend( entries, mode, fname, sha1, log, path );

      continue;


    else: #new root
      _trgt = resmap[0]
      _path = resmap[1]
      
      if (_path != ''):
      
        if (mode[0] != '1'): #dir
          _sha1 = _MangleTree(sha1, DIRS.NEWOBJS + '/' + _trgt, log, indent + 1, '%s/%s' % (path, fname), 1) 
        else:
          _sha1 = None


        if (_path == '/'):
          if (mode[0] != '1'): #dir      
            _TreeAddDir(mt_tree, _trgt, log, path, _sha1)
          else: #file
            _TreeAddDir(mt_tree, _trgt, log)
            _mt = mt_tree[_trgt][3]

        else: #not root
          _pathelements = _path.split('/')
          _TreeAddDir(mt_tree, _trgt, log)
          _mt = mt_tree[_trgt][3]
          for i, elm in enumerate(_pathelements):
            print('dddd: %d,%s %d' % (i, elm, len(_pathelements)-1), file=log)
          
            if (i == len(_pathelements)-1): 
              _TreeAddDir(_mt, elm, log, path, _sha1)
            else:
              _TreeAddDir(_mt, elm, log)
            _mt = _mt[elm][3]


        if (mode[0] == '1'): #file and not root
          if (len(resmap) == 3): #rename
            _fname = resmap[2]
          else:
            _fname = fname
            
          #FIXME: lookup fixed file sha here
          _sha1 = _LookupFile(_trgt, sha1, mode, fname, _fname, log);
          _TreeAppend( _mt, mode, _fname, _sha1, log, path)
          
          _DumpTree('>', _mt, log);
          continue;
          
      else: #path = '' => godeepr
        _MangleTree(sha1, target, log, indent+1, '%s/%s' % (path, fname), justmount)
        continue;

      #if (len(resmap) == 3):
      #  #rename
        
      continue;
    

  # end of loop

  if (indent == 0):
    print("INF: L0 dump mt_tree", file=log);
    _DumpTree('>', mt_tree, log);

    split_trees = _RootMaterializeTree( mt_tree, DIRS.NEWOBJS, '', log);
    return split_trees;

  # non-zero indent code

  if (len(entries) > 0):
    if (target == DIRS.NEWOBJS):
      print("EEE: Unsolicited write to objdir: %s %d %s %d" % (target, indent, path, len(entries)), file=log)
      print(entries.values(), file=log);
      res = root_sha1
    else:
      res = WriteGitTree(entries.values(), target)

    collision = _tree_cache.setdefault(treekey, res.raw)
    if (collision != res.raw):
      print("INF: indent: %d, orig_sha1: %s, res_sha1: %s, collision: %s" % (indent, root_sha1.hex, res.hex, SHA1(collision).hex), file=log);

      
  else:
    print("INF: i%d replace self with inner: len(entries) = %d" % (indent, len(entries)), file=log);
    sys.stdout.flush();
#     assert(len(entries) == 0)
    res = SHA1(b'00000000000000000000');
    

      
  log.flush();
  #assert(collision == res.raw)
  return res



def _TranslateOneTree(treeish):
  p = multiprocessing.current_process()

  log = open('log/rt-%d.log' % p.pid, 'a')
  
  print('hello from process %s with pid %s' % (p.name, p.pid), file=log)
  try:
    # Do not bother checking if we already translated the tree. It is extremely
    # unlikely (i.e. empty commits) and is not worth the overhead of checking.

    # tree part cache
    mt_tree.clear();

    split_trees = _MangleTree(SHA1.FromHex(treeish), DIRS.NEWOBJS, log, 0, '', 0)

    if (split_trees is None): #empty tree
      return;

    for repo in split_trees:
      key = "%s:%s" % (treeish, repo)
      _mangled_sha = split_trees[repo]
      
      _root_trees.setdefault(key, _mangled_sha.hex)
      
#   assert(collision == mangled_sha1.hex)

    sys.stdout.flush();
    sys.stderr.flush();
    
  except Exception as e:
    log.write('\n' + traceback.format_exc());
    log.flush();

    sys.stderr.write('\npid: %d' % p.pid)
    sys.stderr.write('\n' + traceback.format_exc())
    sys.stderr.flush();

    raise


def _TimeToStr(seconds):
  tgmt = time.gmtime(seconds)
  return time.strftime('%Hh:%Mm:%Ss', tgmt)


def _RewriteTrees(trees):
  pool = multiprocessing.Pool( min(4, int(multiprocessing.cpu_count())*2) )

  pending = len(trees)
  done = 0
  tstart = time.time()
  checkpoint_done = 0
  checkpoint_time = tstart
  for _ in pool.imap_unordered(_TranslateOneTree, trees, 5):
    done += 1
    now = time.time()
    done_since_checkpoint = done - checkpoint_done
    if done == pending or (done % 2) == 1:
      compl_rate = (now - checkpoint_time) / done_since_checkpoint
      eta = _TimeToStr((pending - done) * compl_rate)
      print('\r%d / %d Trees rewritten (%.1f trees/sec), ETA: %s      ' % (done, pending, 1 / compl_rate, eta) )
      sys.stdout.flush()
    # Keep a window of the last 5s of rewrites for ETA calculation.
#    if now - checkpoint_time > 5:
#      checkpoint_done = done
#      checkpoint_time = now

  pool.close()
  pool.join()
  elapsed = time.time() - tstart
  print('\nTree rewrite completed in %s (%.1f trees/sec)' % ( _TimeToStr(elapsed), done / elapsed) );



def _RewriteCommits(targets, revs):
  root_trees = _root_trees.copy()  # Un-proxied local copy for faster lookups.

  total = len(revs)*len(targets)
  done = 0
  tstart = time.time()

  for target in targets:
    _prev_commit_tree = None
    last_parent = None
    last_rewritten_parent = None
    
    for rev in revs:
      objtype, objlen, payload = ReadGitObj(SHA1.FromHex(rev), DIRS.ORIGOBJS)
      assert(objtype == 'commit')
      assert(payload[0:5] == 'tree ')  # A commit obj should begin with a tree ptr
      orig_tree = payload[5:45]
    
      key = "%s:%s" % (orig_tree, target)
      if not (key in root_trees):
        continue;
      
      new_tree = root_trees[key]
      assert(len(new_tree) == 40)
      
      if new_tree == _prev_commit_tree:
        #no-change commit
        continue;
      
      _prev_commit_tree = new_tree
      
      new_payload = 'tree ' + new_tree + '\n'

      if last_parent:
        new_payload += 'parent ' + last_rewritten_parent + '\n'

      parent = None
      if (payload[46:52] != 'parent'):
        new_payload += payload[46:]
      else:
        assert(payload[46:52] == 'parent')
        new_payload += payload[94:]

      last_parent = rev
      sha1 = WriteGitObj('commit', new_payload, DIRS.NEWOBJS + '/' + target)
      last_rewritten_parent = sha1.hex
      
      done += 1
      
      if done % 100 == 1 or done == len(revs)*len(targets):
        compl_rate = (time.time() - tstart) / done
        eta = _TimeToStr((total - done) * compl_rate)
        print('\r%d / %d Commits rewritten (%.1f commits/sec), ETA: %s      ' % (done, total, 1 / compl_rate, eta) )
        sys.stdout.flush()

    print('\n')
    print('Your new head for %s is %s (which corresponds to %s)' % (target, last_rewritten_parent, last_parent) )





# collect file for charset conv
def _CollectTree( root_sha1, target, indent, path, log, justmount):
  key = target[-4:] + root_sha1.hex
  
  if (key in _local_collected_cache):
    collected_tree = _local_collected_cache[key]
  else:
    collected_tree= _collected_tree.get(key)
    
  if collected_tree and (indent > 4):
    _local_collected_cache[key] = 1
    
    d = {}
    d[target] = []
    return d


  files = OrderedDict({});
  if (target != ''):
    files[target] = [];
  
  for mode, fname, sha1 in ReadGitTree(root_sha1, DIRS.ORIGOBJS):

    if (indent < 7) and (justmount == 0):
      resmap = _TreePathMapping(indent, fname, path, log)
    else:
      resmap = ('unk','')
      
    print('>  %d %s %s %s/%s :%d => %s:%s' % ( indent, mode, sha1.hex, path, fname, justmount, resmap[0], resmap[1]), file=log);


    if resmap[0] == 'godeepr':
      _files = _CollectTree( sha1, target, indent+1, '%s/%s' % (path, fname), log, justmount)
      for _key in _files:
        if not (_key in files):
          files[_key] = _files[_key]
        else:
          files[_key].extend( _files[_key] )
      
      continue;

    elif resmap[0] == 'drop':
      continue;
     
    elif resmap[0] == 'unk':
      if mode[0] == '1':  # It's a file
        _, ext = os.path.splitext(fname)
      
        if fname == '.gitignore':
          continue;
      
        elif ext.lower() in _KILL_EXTS:
          # skip adding
          continue;
          
        elif ext.lower() in _BIN_EXTS:
          # no-transform, skip, add as-is later
          continue; 

        else:
          files[target].append( sha1.raw )
          continue;
    
      else:	#dir
        assert(mode == '40000')

        _files = _CollectTree(sha1, target, indent + 1,'%s/%s' % (path, fname), log, justmount);
        for _key in _files:
          files[_key].extend( _files[_key] )
          
        continue;

    else: #new mapping
      _trgt = resmap[0]
      
      if not (_trgt in files):
        files[_trgt] = [];
      
      if mode[0] == '1':
        files[_trgt].append( sha1.raw )
      else:
        _files = _CollectTree(sha1, _trgt, indent + 1,'%s/%s' % (path, fname), log, 1)
        for _key in _files:
          files[_key].extend( _files[_key] )
    
  _collected_tree.setdefault( key, 1 )
  _local_collected_cache[key] = 1
  
  if(indent == 0):
      for _key in files:
        print('< %d %s, %s %d' % (indent, path, _key, len(files[_key])), file=log)
  
  return files;


def _CollectOneTree(treeish):
  p = multiprocessing.current_process()

  log = open('log/ct-%d.log' % p.pid, 'a')
  
  print('hello from process %s with pid %s' % (p.name, p.pid), file=log)
  try:
    # Do not bother checking if we already translated the tree. It is extremely
    # unlikely (i.e. empty commits) and is not worth the overhead of checking.
    collected_files = _CollectTree(SHA1.FromHex(treeish), '', 0, '', log, 0)
    #print('done: %s: %d files' % (treeish, len(collected_files)))
    return collected_files
    
  except Exception as e:
    log.write('\n' + traceback.format_exc());
    log.flush();

    sys.stderr.write('\npid: %d' % p.pid)
    sys.stderr.write('\n' + traceback.format_exc())
    sys.stderr.flush();

    raise


def _CollectTrees( trees, log ):
  files = {}
  pool = multiprocessing.Pool( min(8, int(multiprocessing.cpu_count())*2) )

  pending = len(trees)
  done = 0
  tstart = time.time()
  checkpoint_done = 0
  checkpoint_time = tstart
  _total = 0

  for result in pool.imap_unordered(_CollectOneTree, trees, min(5, len(trees) / 5)):
    for _key in result:
      for _sha in result[_key]:
        if not _sha in files:
          files[ _sha ] = _key
          _total = _total+1
        elif files[ _sha ] == _key:
          continue;
        elif isinstance(files[_sha], str):
          print("duplicate file: %s in %s, %s" % ( SHA1(_sha).hex, files[_sha], _key), file=log)
          files[ _sha ] = { files[ _sha ]:1, _key:1 }
          _total = _total+1
        elif not (_key in files[ _sha ]):
          files[ _sha ][ _key ] = 1
          _total = _total+1

    done += 1
    now = time.time()
    done_since_checkpoint = done - checkpoint_done
    if done == pending or (done % 10) == 1:
      compl_rate = (now - checkpoint_time) / done_since_checkpoint
      eta = _TimeToStr((pending - done) * compl_rate)
      print('\r%d / %d Trees collected (%.1f trees/sec), ETA: %s, files: %d/%d      ' % (done, pending, 1 / compl_rate, eta, len(files), _total) )
      sys.stdout.flush()

  pool.close()
  pool.join()
  elapsed = time.time() - tstart
  print('\nTree collect completed in %s (%.1f trees/sec), %d files' % ( _TimeToStr(elapsed), done / elapsed, len(files) ) );

  #  for _key in files:
  #    print("> Collected %s: %d" % ( _key, len(files[_key])), file=log)

  return files;


def _Transform( payload ):
  payload = payload.replace('\xef\xbb\xbf', '').replace('\r\n', '\n').replace('<speach', '<speech').replace('</speach>','</speech>');
  _payload = '';
  while (_payload != payload):
    _payload = payload;
    payload = _payload.replace('\n\n\n\n','\n\n').replace('\n\n\n', '\n\n').replace(' \n', '\n');

  return payload


def _ConvertFile( sha1, target, log ):
#  cached_file = _file_cache.get(sha1.raw)
#  if (cached_file):
#    return cached_file;

  otype, ln, payload = ReadGitObj(sha1, DIRS.ORIGOBJS)
  enc = _GuessGitFileEnc( sha1, payload, log );

  if (enc == 'UTFXML') or (enc == 'UTFDET') or (enc == 'ASCII'):
    # no change
    new_file_sha1 = WriteGitObj(otype, _Transform(payload), target);

  elif (enc == 'UTFBOM'):
    new_file_sha1 = WriteGitObj(otype, _Transform(payload[3:]), target);

  elif (enc == 'WINXML') or (enc == 'WINDET'):
    new_payload = payload.replace('\x98', '\x20').decode('windows-1251').replace('<?xml version="1.0" encoding="windows-1251"', '<?xml version="1.0" encoding="utf-8"').encode('utf-8');
    new_file_sha1 = WriteGitObj(otype, _Transform(new_payload), target);
  else:
    # no change
    new_file_sha1 = WriteGitObj(otype, payload, target);
    assert( sha1.raw == new_file_sha1.raw )

  key = target[-4:] + sha1.hex

  _file_cache.setdefault( key, new_file_sha1.raw );
  _local_file_cache.setdefault( key, new_file_sha1.raw );

  return new_file_sha1.raw


def _ConvertOneFile( tuple ):
  p = multiprocessing.current_process()

  log = open('log/fc-%d.log' % p.pid, 'a')
  
  print('hello from process %s with pid %s' % (p.name, p.pid), file=log)
  try:
    # Do not bother checking if we already translated the tree. It is extremely
    # unlikely (i.e. empty commits) and is not worth the overhead of checking.

    targets = tuple[1]
    if isinstance(targets, str):
      _ConvertFile(SHA1(tuple[0]), DIRS.NEWOBJS+'/'+tuple[1], log)
    else:
      for key in targets:
        print("III: multitarget: %s %s" % (SHA1(tuple[0]).hex, key), file = log);
        _ConvertFile(SHA1(tuple[0]), DIRS.NEWOBJS+'/'+key, log)
    
  except Exception as e:
    log.write('\n' + traceback.format_exc());
    log.flush();

    sys.stderr.write('\npid: %d' % p.pid)
    sys.stderr.write('\n' + traceback.format_exc())
    sys.stderr.flush();

    raise



def _ConvertFiles( files, log ):
  pool = multiprocessing.Pool( min(32, int(multiprocessing.cpu_count())*2) )

  pending = len(files)
  done = 0
  tstart = time.time()
  checkpoint_done = 0
  checkpoint_time = tstart
  for result in pool.imap_unordered(_ConvertOneFile, files.items(), 1000):
    done += 1
    now = time.time()
    done_since_checkpoint = done - checkpoint_done
    if done == pending or (done % 1000) == 0:
      compl_rate = (now - checkpoint_time) / done_since_checkpoint
      eta = _TimeToStr((pending - done) * compl_rate)
      print('\r%d / %d Files processed (%.1f files/sec), ETA: %s      ' % (done, pending, 1 / compl_rate, eta) )
      sys.stdout.flush()

  pool.close()
  pool.join()
  elapsed = time.time() - tstart
  print('\nFile processing completed in %s (%.1f files/sec)' % ( _TimeToStr(elapsed), done / elapsed ) );


def _ListTargets(base):
  targets = []
  for f in os.listdir(base):
    if os.path.isdir(os.path.join(base, f)):
      targets.append(f)

  return targets


def main():

  param = 5000
  print('Processing no more than %d commits' % param);

  print('New git objects:', DIRS.NEWOBJS)
  Makedirs(DIRS.NEWOBJS)

  DIRS.ORIGOBJS = '/mnt/d_scratch/loose/objects'
  print('Orig objects:', DIRS.ORIGOBJS)

  if not _SKIP_COPY_INTO_CGS:
    print('GCS staging area:', DIRS.GCS)
    Makedirs(DIRS.GCS)
  else:
    print('WARNING: Omitting GCS object generation.')

  print('')
  revs = []
  trees = []

  if len(sys.argv) > 1:
    print('Reading cached rev-list + trees from ' + sys.argv[1])
    reader = open(sys.argv[1])
  else:
    cmd = ['git', 'rev-list', '--format=%T', '--reverse', 'master']
    print('Running [%s], might take a while' % ' '.join(cmd))
    proc = subprocess.Popen(cmd, stdout=subprocess.PIPE, bufsize=1048576)
    reader = proc.stdout

  # The output of rev-list will be as follows:
  # commit abcdef1234 <- commit-ish (irrelevant for us here)
  # 567890abcdef      <- tree-ish
  # commit ....
  while True:
    line = reader.readline()
    if not line:
      break
    line = line.rstrip('\r\n')
    if line.startswith('commit'):
      rev = line[7:]
      assert(len(rev) == 40)
      revs.append(rev)
      continue
    else:
      assert(len(line) == 40)
      trees.append(line)

  assert(len(revs) == len(trees))
  print('Got %d revisions to rewrite' % len(revs))

  print('\nStep 1: Collect file names and hashes to fix charset');
  shafiles = _CollectTrees(trees[0:param], sys.stdout);

  print('\nStep 2: Rewrite files in parallel: %d' % len(shafiles) );
  _ConvertFiles(shafiles, sys.stdout);

  print('\nDumping sha file map\n');
  with open('shamap.txt', 'w') as f:
    for key in shafiles:
      orig_sha = SHA1(key)
      targets = shafiles[key];
      
      if isinstance(targets, str):
        targets = [ targets ];

      for target in targets:
        key = target[-4:] + orig_sha.hex

        new_sha = _file_cache.get(key)
        
        if new_sha:
          print('%s %d %s %s' % (orig_sha.hex, len(targets), target, SHA1(new_sha).hex), file=f)
        else:
          print('%s %d %s None' % (orig_sha.hex, len(targets), target), file=f)

  print('\nStep 3: Rewriting trees in parallel')
  _RewriteTrees(trees[0:param])

  print('\nStep 3: Rewriting commits serially')
  targets = _ListTargets(DIRS.NEWOBJS)
  _RewriteCommits(targets, revs[0:param])

  print('You should now run git fsck NEW_HEAD_SHA. You are a fool if you don\'t')
#  sys.exit(1);

if __name__ == '__main__':
  sys.exit(main())
