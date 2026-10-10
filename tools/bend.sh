#!/usr/bin/env bash
# Build Bend 2 from its flake into a cache, then run it on the arguments.
#
# Bend 2 is not in nixpkgs. The `bend` package there at 0.2.x is Bend 1, a
# different language from the same lineage. Bend 2 ships a flake, so nix can
# build it straight from the repository.
#
# Set BEND_CACHE to move the build. The default is ~/.cache/bend2.
set -euo pipefail
CACHE="${BEND_CACHE:-$HOME/.cache/bend2}"
BIN="$CACHE/result/bin/bend"
if [ ! -x "$BIN" ]; then
  mkdir -p "$CACHE"
  echo "building Bend 2 into $CACHE" >&2
  nix build --no-write-lock-file \
    --extra-experimental-features 'nix-command flakes' \
    github:bendlang/bend -o "$CACHE/result"
fi
exec "$BIN" "$@"
