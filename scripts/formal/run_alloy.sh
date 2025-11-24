#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$SCRIPT_DIR/../.." && pwd)
WORKDIR="$ROOT/docs/spec/alloy"
ALLOY_FILE="$WORKDIR/boundary.als"
CACHE="$ROOT/.cache/formal"
JAR="$CACHE/alloy.jar"
IMG="eclipse-temurin:21-jre"

if [[ ! -f $ALLOY_FILE ]]; then
  echo "Alloy file not found: $ALLOY_FILE" >&2
  exit 1
fi

mkdir -p "$CACHE"

if [[ ! -f $JAR ]]; then
  echo "[Alloy] downloading org.alloytools.alloy.dist.jar" >&2
  curl -fsSL -o "$JAR" https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v6.0.0/org.alloytools.alloy.dist.jar
fi

compile_run_local() {
  echo "[Alloy] executing checks via SimpleCLI"
  java -cp "$JAR" edu.mit.csail.sdg.alloy4whole.SimpleCLI "$ALLOY_FILE"
}

compile_run_docker() {
  echo "[Alloy] running via docker ($IMG)"
  docker run --rm \
    -v "$WORKDIR:/work" \
    -v "$CACHE:/cache" \
    "$IMG" sh -c "java -cp /cache/alloy.jar edu.mit.csail.sdg.alloy4whole.SimpleCLI /work/boundary.als"
}

if command -v java >/dev/null 2>&1 && command -v javac >/dev/null 2>&1; then
  compile_run_local
else
  compile_run_docker
fi
