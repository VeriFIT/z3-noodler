#!/bin/bash
# build_reduce_stats_variant.sh [NAME]
# Builds build/$PRESET/variants/NAME/z3 (PRESET release-g = release with -g, NAME reduce-stats by default) for the reduce statistics:
# no reduce guards (RED_BOUND and INTERSECTION_RED_BOUND replaced by ~0u in their users), the context tags of variant-src/reduce-stats.patch
# in regex.cpp, and reduce_wrap.cpp linked as the wrapper of mata::nfa::reduce (logs every call to $REDUCE_LOG).
set -euo pipefail
name=${1:-reduce-stats}
repo=${REPO:-/home/koumy/Documents/z3-noodler}
export REPO=$repo PRESET=${PRESET:-release-g}
tools=$repo/perf-tools
bdir=$repo/build/$PRESET
vdir=$bdir/variants/$name
noodler=src/smt/theory_str_noodler
users="regex.cpp memb_heuristics_procedures.cpp theory_str_noodler_final_check.cpp"

mkdir -p "$vdir/src"
for f in $users; do cp "$repo/$noodler/$f" "$vdir/src/"; done
patch -s -d "$vdir/src" -p1 < "$tools/variant-src/reduce-stats.patch"
sed -i -E 's/\b(regex::)?(INTERSECTION_)?RED_BOUND\b/(~0u)/g' "$vdir"/src/*.cpp

# the wrapper, compiled with the flags of regex.cpp
cd "$bdir"
obj_rel=$(ninja -t targets all | grep -o "^[^:]*/theory_str_noodler/regex\.cpp\.o" | head -1)
compile=$(ninja -t commands -s "$obj_rel")
compile=${compile/-MD -MT $obj_rel -MF $obj_rel.d /}
compile=${compile/-o $obj_rel -c $repo\/$noodler\/regex.cpp/-o $vdir/reduce_wrap.o -c $tools/reduce_wrap.cpp}
eval "$compile"

sym=$(sed -n 's/^#define REDUCE_SYM "\(.*\)"$/\1/p' "$tools/reduce_wrap.cpp")
replacements=()
for f in $users; do replacements+=("$noodler/$f=$vdir/src/$f"); done
LINK_EXTRA="$vdir/reduce_wrap.o -Wl,--wrap=$sym" "$tools/build_variant.sh" "$name" "${replacements[@]}"
