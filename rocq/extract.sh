#!/bin/sh
# Regenerate rocq/extracted/ from the proofs, or check it is current.
#
# The extracted scan is CHECKED IN, because Rocq lives in a different
# opam switch from the project's OCaml deps and `dune build` must not
# need it. Checked-in generated code can drift from what generates it,
# so --check regenerates into a scratch copy and compares, restoring the
# tree either way. That is the form to run in CI.
set -eu

check=false
case "${1-}" in
  --check) check=true ;;
  "") ;;
  *) echo "usage: $0 [--check]" >&2; exit 2 ;;
esac

root=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
cd "$root"

# Rocq is taken from the current environment, or from the opam switch
# named by ROCQ_SWITCH if it is set.

saved=$(mktemp -d)
trap 'rm -rf "$saved"' EXIT
cp rocq/extracted/layout_scan.ml rocq/extracted/layout_scan.mli "$saved/"

( if [ -n "${ROCQ_SWITCH-}" ]; then
    eval "$(opam env --switch="$ROCQ_SWITCH" --set-switch)"
  fi
  cd rocq
  rocq makefile -f _RocqProject -o Makefile >/dev/null
  make >/dev/null )

if $check; then
  if cmp -s "$saved/layout_scan.ml" rocq/extracted/layout_scan.ml \
     && cmp -s "$saved/layout_scan.mli" rocq/extracted/layout_scan.mli; then
    echo "rocq/extracted is up to date"
  else
    echo "rocq/extracted is stale; rerun rocq/extract.sh" >&2
    diff -u "$saved/layout_scan.mli" rocq/extracted/layout_scan.mli >&2 || true
    cp "$saved/layout_scan.ml" "$saved/layout_scan.mli" rocq/extracted/
    exit 1
  fi
else
  echo "wrote rocq/extracted/layout_scan.{ml,mli}"
fi
