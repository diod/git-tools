#!/bin/bash

umount /mnt/d_scratch/tmp || exit 1

mount -t tmpfs none /mnt/d_scratch/tmp -o size=40g,noatime,nr_inodes=0 || exit 1

rm -vf log/*log;

nice -n 15 python2.7 history-rewrite.py origin/rev-list.txt 2>&1 | tee rewrite.log

for F in config  description  HEAD  hooks  info  refs; do
  rsync -av loose/$F tmp/$F || exit 1;
done;

HASH=$(tail -n 2 rewrite.log |head -n 1|sed -e "s/^.* is //" -e "s/ .*$//")


echo 
echo "Runnging git fsck ${HASH} ..."
echo 

cd tmp;

git fsck $HASH 2>&1 | tee fsck.log

echo
echo Update and expire

git update-ref refs/heads/master $HASH
git reflog expire --expire=now --all

echo
echo git pack
echo

nice -n 15 git repack -a -d || exit 1;

rsync -avc --delete /mnt/d_scratch/tmp/ /mnt/d_scratch/converted/
