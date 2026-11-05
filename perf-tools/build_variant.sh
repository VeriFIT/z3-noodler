#!/bin/bash
# build_variant.sh NAME SRC=REPLACEMENT...
# Builds build/release/variants/NAME/z3: the release z3 where each repo source SRC (e.g.
# src/smt/theory_str_noodler/regex.cpp) is compiled from REPLACEMENT (a file, or a git revision to take SRC from);
# all other objects are reused from build/release. Headers placed next to a replacement shadow the original ones.
# LINK_EXTRA: objects and flags added to the link before the libraries (e.g., a wrapper object and -Wl,--wrap=SYM).
set -euo pipefail
name=$1; shift
repo=${REPO:-/home/koumy/Documents/z3-noodler}
bdir=$repo/build/${PRESET:-release}
vdir=$bdir/variants/$name
mkdir -p "$vdir"
cd "$bdir"
link=$(ninja -t commands -s z3)
for spec in "$@"; do
    src=${spec%%=*}; repl=${spec#*=}
    base=$(basename "$src" .cpp)
    obj_rel=$(ninja -t targets all | grep -o "^[^:]*/$(basename "$(dirname "$src")")/${base}\.cpp\.o" | head -1 || true)
    [ -n "$obj_rel" ] || { echo "no object for $src"; exit 1; }
    if [ -f "$repl" ]; then cp "$repl" "$vdir/$base.cpp"
    else git -C "$repo" show "$repl:$src" > "$vdir/$base.cpp"; fi
    compile=$(ninja -t commands -s "$obj_rel")
    compile=${compile/-MD -MT $obj_rel -MF $obj_rel.d /}
    compile=${compile/-o $obj_rel -c $repo\/$src/-I$repo/$(dirname "$src") -o $vdir/$base.o -c $vdir/$base.cpp}
    eval "$compile"
    link=${link/ $obj_rel / $vdir/$base.o }
done
link=${link/--dependency-file=src\/shell\/CMakeFiles\/shell.dir\/link.d/--dependency-file=$vdir/link.d}
link=${link/ -o z3 / -o $vdir/z3 ${LINK_EXTRA:-} }
eval "$link"
ls -la "$vdir/z3"
