#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$SCRIPT_DIR/../.." && pwd)
WORKDIR="$ROOT/docs/spec/tlaplus"
TLA_FILE="$WORKDIR/pce_memory.tla"
CFG_FILE="${TLA_CFG:-$WORKDIR/pce_memory.cfg}"
CACHE="$ROOT/.cache/formal"
JAR="$CACHE/tla2tools.jar"
IMG="eclipse-temurin:21-jre"

if [[ ! -f $TLA_FILE ]]; then
  echo "TLA file not found: $TLA_FILE" >&2
  exit 1
fi

mkdir -p "$CACHE"

if [[ ! -f $JAR ]]; then
  echo "[TLA+] downloading tla2tools.jar"
  curl -fsSL -o "$JAR" https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar
fi

if command -v tlc >/dev/null 2>&1; then
  echo "[TLA+] running TLC locally"
  tlc -config "$CFG_FILE" "$TLA_FILE"
  exit $?
fi

echo "[TLA+] running via docker ($IMG)"
docker run --rm \
  -v "$WORKDIR:/work" \
  -v "$CACHE:/cache" \
  "$IMG" sh -c "java -jar /cache/tla2tools.jar -config /work/pce_memory.cfg /work/pce_memory.tla"
