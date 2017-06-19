#!/bin/bash
echo Running on $1
rm result
touch result
for file in $1/*; do
  echo $file
  t=`(time $2 $file > /dev/null) 2>&1 >/dev/null | grep 'real' | awk '{print $2}'`
  echo $t $file >> result
done
sort -r result -o result