#!/bin/bash

umount /mnt/d_scratch/tmp || exit 1

mount -t tmpfs none /mnt/d_scratch/tmp -o size=40g,noatime,nr_inodes=0 || exit 1

rm -vf log/*log;

nice -n 15 python2.7 history-rewrite.py origin/rev-list.txt 2>&1 | tee rewrite.log

if [ ${PIPESTATUS[0]} -ne 0 ]; then
  echo "Error exit";
  exit 1;
fi;

echo "running fsck on repos"

mkdir -p /mnt/d_scratch/converted

while read REPO SHA; do
  echo $REPO $SHA;
  
  mkdir /mnt/d_scratch/tmp/$REPO/objects
  mv /mnt/d_scratch/tmp/$REPO/[a-f0-9][a-f0-9] /mnt/d_scratch/tmp/$REPO/objects/
  
  for F in config description  HEAD  hooks  info  refs; do
    rsync -a loose/$F tmp/$REPO/$F || exit 1;
  done;
    
  if [ "$SHA1" == "None" ]; then
    echo "FIXME";
    continue;
  fi;
    
  cd /mnt/d_scratch/tmp/$REPO
  echo "## git fsck"
  git fsck $SHA 2>&1 | tee fsck.log
  git update-ref refs/heads/master $SHA

  cd /mnt/d_scratch

done< <( tail -n 1000 rewrite.log |grep "Your new head"|sed -e "s/^.*for \([0-9a-z_]\+\) is \([Non0-9a-f]\+\) .*/\1 \2/" );

#Your new head for accent is d0318e8baf2632a153bbae31703167c54d3611ce (which corresponds to 6b6abef99521ab377844c3c2c0b370e0335fdebc)

#
#
echo "git packing"


while read REPO SHA; do
  echo $REPO $SHA;

  cd /mnt/d_scratch/tmp/$REPO

  git reflog expire --expire=now --all
  nice -n 15 git repack -a -d || exit 1;

  rsync -avc --delete /mnt/d_scratch/tmp/$REPO/ /mnt/d_scratch/converted/$REPO/

  cd /mnt/d_scratch

done< <( tail -n 1000 rewrite.log |grep "Your new head"|sed -e "s/^.*for \([0-9a-z_]\+\) is \([Non0-9a-f]\+\) .*/\1 \2/" );

