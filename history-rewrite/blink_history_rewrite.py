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
from array import array

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
  NEWOBJS = '/mnt/d_scratch/tmp/objects'

  # Where the binary files (then uploaded to GCS) will be moved.
  GCS = '/mnt/d_scratch/gcs-bucket/'


# _tree_cache is a map of tree-ish -> translated tree-ish and is used to avoid
# re-translating sub-trees which are identical between subsequent commits
_tree_cache = multiprocessing.Manager().dict()

# collected tree
_collected_tree = multiprocessing.Manager().dict()

# A map of <original tree SHA1 (hex)> -> <translated SHA1> for top-level trees.
# Contains the results of _TranslateOneTree calls.
_root_trees = multiprocessing.Manager().dict()

# map for patched files
_file_cache = multiprocessing.Manager().dict()

# set of SHA1s (just to keep the total count)
_gcs_blobs = multiprocessing.Manager().dict()

_local_file_cache = {}
_local_tree_cache = {}

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



def _MangleTree(root_sha1, log, indent=0):
  assert(isinstance(root_sha1, SHA1))
  changed = False
  entries = []

  if root_sha1.raw in _local_tree_cache:
    cached_translation = _local_tree_cache[root_sha1.raw]
  else:
    cached_translation = _tree_cache.get(root_sha1.raw)
  
  if cached_translation:
    _local_tree_cache[root_sha1.raw] = cached_translation
    return SHA1(cached_translation)

  if indent == 0:
    print('\n_mangle_tree_sha: %s' % root_sha1.hex, file=log)

  replace_self_sha1 = None
  base_gitignore_sha1 = None
  for mode, fname, sha1 in ReadGitTree(root_sha1, DIRS.ORIGOBJS):
    old_sha1_raw = sha1.raw
    
    print('>  %d %s %s' % ( indent, mode, fname), file=log);
    
    if mode[0] == '1':  # It's a file
      _, ext = os.path.splitext(fname)
      if fname == '.gitignore':
          entries.append( ( mode, fname, sha1 ) );
          if _file_cache.get( sha1.raw ) is None:
            _file_cache.setdefault( sha1.raw, sha1.raw );

            otype, olen, payload = ReadGitObj(sha1, DIRS.ORIGOBJS);
            new_sha1 = WriteGitObj(otype, payload, DIRS.NEWOBJS)
            assert( sha1.raw == new_sha1.raw )
            
          continue;
      
      elif ext.lower() in _KILL_EXTS:
          # skip adding
          changed = True
          continue;
          
      elif ext.lower() in _BIN_EXTS:
          # add as-is
          entries.append( ( mode, fname, sha1 ) );
          if _file_cache.get( sha1.raw ) is None:
            _file_cache.setdefault( sha1.raw, sha1.raw );

            otype, olen, payload = ReadGitObj(sha1, DIRS.ORIGOBJS);
            new_sha1 = WriteGitObj(otype, payload, DIRS.NEWOBJS)
            assert( sha1.raw == new_sha1.raw )

          continue;

      else:
          if sha1.raw in _local_file_cache:
            cached_file = _local_file_cache[sha1.raw]
          else:
            cached_file = _file_cache.get(sha1.raw)
            _local_file_cache[sha1.raw] = cached_file
            
          if (cached_file):
            entries.append( (mode, fname, SHA1(cached_file)) );
            changed = changed or (sha1.raw != cached_file)
            continue;
      
          print("not-translated: %s %s" % (enc, fname), file=log);
          entries.append( (mode, fname, sha1) );
          continue;

    else:	#dir
      assert(mode == '40000')
      if (indent == 0):
        if (fname == 'ruscorpora'):
          replace_self_sha1 = _MangleTree(sha1, log, indent + 1)
          changed = True
          continue;
        else:
          print("ERR: unknown L0 branch: %s keeping" % fname, file=log);
        
      if (indent == 1):
        if (fname == 'trunk'):
          replace_self_sha1 = _MangleTree(sha1, log, indent + 1)
          changed = True
          continue;
        elif (fname == 'tags') or (fname == 'branches'):
          #drop subtrees
          continue;
        else:
          print("ERR: unknown L1 branch: %s keeping" % fname, file=log);
        
      if (indent == 2):
        #if (fname == 'corpora'):
        #  replace_self_sha1 = _MangleTree(sha1, log, indent + 1)
        #  changed = True
        if (fname == 'www') or (fname == 'saas') or (fname == 'conf') or (fname == 'db') or (fname == 'hooks') or (fname == 'locks') or (fname == 'ruscorpora_suggest') or (fname == 'makeup'):
          #drop
          continue;
        elif (fname == 'standard') or (fname == 'spoken') or (fname == 'accent') or (fname == 'corpora'):
          print("INF: known L2 branch %s" % fname, file=log );
        else:
          print("WRN: unknown L2 branch: %s keeping" % fname, file=log);

      #if in_tests_dir or fname.endswith('Tests'):
      sha1 = _MangleTree(sha1, log, indent + 1)
      changed = True if old_sha1_raw != sha1.raw else changed

    entries.append((mode, fname, sha1))

  # Now add .gitignore in the right place.
  #if in_tests_dir and indent == 1:
  #  # base_gitignore_sha1 maybe None if not present in the original tree.
  #  new_gitignore_sha1 = _BuildGitignoreMaybeCached(base_gitignore_sha1)
  #  entries.append(('100644', '.gitignore', new_gitignore_sha1))
  #  changed = True

  if (replace_self_sha1 is None) or (len(entries) > 0):
    res = WriteGitTree(entries, DIRS.NEWOBJS)
  else:
    print("INF: replace self with inner: len(entries) = %d" % (len(entries)), file=log);
    sys.stdout.flush();
#     assert(len(entries) == 0)
    res = replace_self_sha1
    
  collision = _tree_cache.setdefault(root_sha1.raw, res.raw)
  if (collision != res.raw):
    log.write("INF: indent: %d, orig_sha1: %s, res_sha1: %s, collision: %s" % (indent, root_sha1.hex, res.hex, SHA1(collision).hex));

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
    mangled_sha1 = _MangleTree(SHA1.FromHex(treeish), log)
    collision = _root_trees.setdefault(treeish, mangled_sha1.hex)
    assert(collision == mangled_sha1.hex)

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


def _RewriteCommits(revs):
  root_trees = _root_trees.copy()  # Un-proxied local copy for faster lookups.
  total = len(revs)
  done = 0
  last_parent = None
  last_rewritten_parent = None
  tstart = time.time()
  for rev in revs:
    objtype, objlen, payload = ReadGitObj(SHA1.FromHex(rev), DIRS.ORIGOBJS)
    assert(objtype == 'commit')
    assert(payload[0:5] == 'tree ')  # A commit obj should begin with a tree ptr
    orig_tree = payload[5:45]
    new_tree = root_trees[orig_tree]
    assert(len(new_tree) == 40)
    new_payload = 'tree ' + new_tree + '\n'
    parent = None
    if not last_parent:
      assert(payload[46:52] != 'parent')
      new_payload += payload[46:]
    else:
      assert(payload[46:52] == 'parent')
      parent = payload[53:93]
      assert(parent == last_parent)
      new_payload += 'parent ' + last_rewritten_parent + '\n'
      new_payload += payload[94:]

    last_parent = rev
    sha1 = WriteGitObj('commit', new_payload, DIRS.NEWOBJS)
    last_rewritten_parent = sha1.hex
    done += 1
    if done % 100 == 1 or done == len(revs):
      compl_rate = (time.time() - tstart) / done
      eta = _TimeToStr((total - done) * compl_rate)
      print('\r%d / %d Commits rewritten (%.1f commits/sec), ETA: %s      ' % (done, total, 1 / compl_rate, eta) )
      sys.stdout.flush()

  print('\n')
  print('Your new head is %s (which corresponds to %s)' % (last_rewritten_parent, last_parent) )





# collect file for charset conv
def _CollectTree( root_sha1, indent, log):
  collected_tree= _collected_tree.get(root_sha1.raw)
  if collected_tree:
    return [];
    
  files = [];
  for mode, fname, sha1 in ReadGitTree(root_sha1, DIRS.ORIGOBJS):

    if mode[0] == '1':  # It's a file
      _, ext = os.path.splitext(fname)
      if fname == '.gitignore':
          continue;
      
      elif ext.lower() in _KILL_EXTS:
          # skip adding
          continue;
          
      elif ext.lower() in _BIN_EXTS:
          # add as-is
          continue; 

      else:
          files.append( sha1.raw )
          continue;
    
    else:	#dir
      assert(mode == '40000')
      print('>  %d %s %s' % ( indent, mode, fname), file=log);

      if (indent == 0) and (fname == 'ruscorpora'):
        files.extend( _CollectTree(sha1, indent + 1, log) )
        continue;
        
      if (indent == 1):
        if (fname == 'trunk'):
          files.extend( _CollectTree(sha1, indent + 1, log) )
          continue;
        elif (fname == 'tags') or (fname == 'branches'):
          #drop subtrees
          continue;
        else:
          print("ERR: unknown L1 branch: %s keeping" % fname, file=log);
        
      if (indent == 2):
        if (fname == 'corpora'):
          files.extend( _CollectTree(sha1, indent + 1, log) )
          continue;
        elif (fname == 'www') or (fname == 'saas') or (fname == 'conf') or (fname == 'db') or (fname == 'hooks') or (fname == 'locks') or (fname == 'ruscorpora_suggest') or (fname == 'makeup'):
          #drop
          continue;
        else:
          print("WRN: unknown L2 branch: %s keeping" % fname, file=log);


      # default
      files.extend( _CollectTree(sha1, indent + 1, log) )

  _collected_tree.setdefault( root_sha1.raw, 1 )
  
  return list(set(files));


def _CollectOneTree(treeish):
  p = multiprocessing.current_process()

  log = open('log/ct-%d.log' % p.pid, 'a')
  
  print('hello from process %s with pid %s' % (p.name, p.pid), file=log)
  try:
    # Do not bother checking if we already translated the tree. It is extremely
    # unlikely (i.e. empty commits) and is not worth the overhead of checking.
    collected_files = _CollectTree(SHA1.FromHex(treeish), 0, log)
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
  for result in pool.imap_unordered(_CollectOneTree, trees, 5):
#    print("res: %d files" % len(result));
    for fsha1 in result:
      files[ SHA1(fsha1).hex ] = 1;

    done += 1
    now = time.time()
    done_since_checkpoint = done - checkpoint_done
    if done == pending or (done % 10) == 1:
      compl_rate = (now - checkpoint_time) / done_since_checkpoint
      eta = _TimeToStr((pending - done) * compl_rate)
      print('\r%d / %d Trees collected (%.1f trees/sec), ETA: %s, files: %d      ' % (done, pending, 1 / compl_rate, eta, len(files)) )
      sys.stdout.flush()

  pool.close()
  pool.join()
  elapsed = time.time() - tstart
  print('\nTree collect completed in %s (%.1f trees/sec), %d files' % ( _TimeToStr(elapsed), done / elapsed, len(files) ) );

  return files;


def _Transform( payload ):
  return payload.replace('\r\n', '\n').replace('\n\n\n','\n\n').replace(' \n', '\n').replace('<speach', '<speech').replace('</speach>','</speech>');


def _ConvertFile( sha1, log ):
  cached_file = _file_cache.get(sha1.raw)
  if (cached_file):
    return;
    

  otype, ln, payload = ReadGitObj(sha1, DIRS.ORIGOBJS)
  enc = _GuessGitFileEnc( sha1, payload, log );

  if (enc == 'UTFXML') or (enc == 'UTFDET') or (enc == 'ASCII'):
    # no change
    new_file_sha1 = WriteGitObj(otype, _Transform(payload), DIRS.NEWOBJS);

  elif (enc == 'UTFBOM'):
    new_file_sha1 = WriteGitObj(otype, _Transform(payload[3:]), DIRS.NEWOBJS);

  elif (enc == 'WINXML') or (enc == 'WINDET'):
    new_payload = payload.replace('\x98', '\x20').decode('windows-1251').replace('<?xml version="1.0" encoding="windows-1251"', '<?xml version="1.0" encoding="utf-8"').encode('utf-8');
    new_file_sha1 = WriteGitObj(otype, _Transform(new_payload), DIRS.NEWOBJS);
  else:
    # no change
    new_file_sha1 = WriteGitObj(otype, payload, DIRS.NEWOBJS);
    assert( sha1.raw == new_file_sha1.raw )

  _file_cache.setdefault( sha1.raw, new_file_sha1.raw );



def _ConvertOneFile( treeish ):
  p = multiprocessing.current_process()

  log = open('log/fc-%d.log' % p.pid, 'a')
  
  print('hello from process %s with pid %s' % (p.name, p.pid), file=log)
  try:
    # Do not bother checking if we already translated the tree. It is extremely
    # unlikely (i.e. empty commits) and is not worth the overhead of checking.

    _ConvertFile(SHA1.FromHex(treeish), log)
    
  except Exception as e:
    log.write('\n' + traceback.format_exc());
    log.flush();

    sys.stderr.write('\npid: %d' % p.pid)
    sys.stderr.write('\n' + traceback.format_exc())
    sys.stderr.flush();

    raise



def _ConvertFiles( files, log ):
  pool = multiprocessing.Pool( min(48, int(multiprocessing.cpu_count())*2) )

  pending = len(files)
  done = 0
  tstart = time.time()
  checkpoint_done = 0
  checkpoint_time = tstart
  for result in pool.imap_unordered(_ConvertOneFile, files, 1000):
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

  print('\nStep 3: Rewriting trees in parallel')
  _RewriteTrees(trees[0:param])

  print('\nStep 3: Rewriting commits serially')
  _RewriteCommits(revs[0:param])

  print('You should now run git fsck NEW_HEAD_SHA. You are a fool if you don\'t')


if __name__ == '__main__':
  sys.exit(main())
