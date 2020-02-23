#!/bin/bash

# Watches file for changes and rebuilds it when written.
inotifywait -e close_write,moved_to,create -m "$1" |
while read -r directory events filename
do
  echo $directory, $events, $filename
  if [ ${filename: -4} == ".dot" ] && [ "$events" = "CLOSE_WRITE,CLOSE" ]
  then
    basename=$(echo "${filename}" | cut -f 1 -d '.')
    dot -T png -o "${basename}.png" "$filename"
  fi
done
