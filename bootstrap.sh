#!/bin/sh
arg0="$0"
docmd="$1"
if [ -z "${docmd}" ]; then
  docmd="clone"
fi
cur_dir="$(pwd)"
clone() {
  if [ -z "$2" ]; then
    git clone "https://github.com/peterhj/$1" "../$1"
  else
    git clone -b "$2" "https://github.com/peterhj/$1" "../$1"
  fi
}
merge() {
  cd "../$1"
  git fetch origin
  if [ -z "$2" ]; then
    git merge --ff-only origin
  else
    git merge --ff-only "origin/$2"
  fi
}
build() {
  if [ "${docmd}" = "clone" ]; then
    clone "$1" "$2"
  elif [ "${docmd}" = "merge" ]; then
    merge "$1" "$2"
  else
    echo "usage: ${arg0} [clone|merge]"
    cd "${cur_dir}"
    exit 1
  fi
}
build byteorder
build cfg_if patch
build fxhash patch
build getrandom patch
build libc
build regex patch
build rng
build rustc_serialize patch
build smol_str patch
build time-0.1 patch-0.1
cd "${cur_dir}"
