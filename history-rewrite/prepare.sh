#!/bin/bash

cd /mnt/d_scratch || exit 1

echo "Update origin rev-list"
cd origin
git rev-list --format=%T --reverse git-svn >rev-list.txt || exit 1
cd ..

echo "Remove loose" && rm -Rf loose && mkdir loose

echo "Init loose repo and unpack"
cd loose
git init --bare

# Let's not get GC in our way
git config gc.auto 0

# Enable standalone gzip compr to loose objects.
git config --global core.loosecompression 5

# This can speed up pack files walking.
git config core.deltaBaseCacheLimit 2G

date

# Decompress all the packs (takes 1-2 hours)
I=1;
for P in $(find /mnt/d_scratch/origin -name '*.pack'); do
  git unpack-objects < "$P" &
  pids[${I}]=$!
  I=$(( I + 1 ))
done



for pid in ${pids[*]}; do
    echo "waiting for $pid"
    wait $pid
    echo $pid done
done

rsync -av /mnt/d_scratch/origin/.git/objects/[0-9a-f][0-9a-f] ./objects

date

cd ..
