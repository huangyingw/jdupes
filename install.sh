#!/bin/zsh -
SCRIPT=$(realpath "$0")
SCRIPTPATH=$(dirname "$SCRIPT")
cd "$SCRIPTPATH"

make clean \
    && make \
    && make install \
    && ~/loadrc/gitrc/g.sh
