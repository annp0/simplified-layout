#!/bin/sh
# Regenerate coq/extracted/ from the proofs, or check it is current.
#
# The extracted scan is CHECKED IN, because Coq lives in a different
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

COQ_SWITCH=${COQ_SWITCH:-vst-audit}

saved=$(mktemp -d)
trap 'rm -rf "$saved"' EXIT
cp coq/extracted/layout_scan.ml coq/extracted/layout_scan.mli "$saved/"

( eval "$(opam env --switch="$COQ_SWITCH" --set-switch)"
  make -C coq >/dev/null )

if $check; then
  if cmp -s "$saved/layout_scan.ml" coq/extracted/layout_scan.ml \
     && cmp -s "$saved/layout_scan.mli" coq/extracted/layout_scan.mli; then
    echo "coq/extracted is up to date"
  else
    echo "coq/extracted is stale; rerun coq/extract.sh" >&2
    diff -u "$saved/layout_scan.mli" coq/extracted/layout_scan.mli >&2 || true
    cp "$saved/layout_scan.ml" "$saved/layout_scan.mli" coq/extracted/
    exit 1
  fi
else
  echo "wrote coq/extracted/layout_scan.{ml,mli}"
fi
