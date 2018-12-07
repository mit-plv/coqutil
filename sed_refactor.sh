#!/bin/sh

# move some .v files, "git add" them, then run this script to obtain a sed command which might refactor the Imports and qualified names
# this script doesn't modify anything, it just prints a long sed command which you can choose to run or discard

echo -n 'find . -type f -name '"'"'*.v'"'"' -print0 | xargs -0 sed -i ' && git status | grep -e 'renamed:' | sed -e 's/\t//g' -e 's/\//./g' -e 's/renamed: *src\.\([^.]*\)\.v -> src\.\(.*\)\.v/-e '"'"'s\/\\.\1\/.\2\/g'"'"'/g' | tr '\n' ' ' && echo ''
