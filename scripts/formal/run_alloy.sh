#!/usr/bin/env bash
set -euo pipefail

SCRIPT_DIR=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$SCRIPT_DIR/../.." && pwd)
WORKDIR="$ROOT/docs/spec/alloy"
CACHE="$ROOT/.cache/formal"
JAR="$CACHE/alloy.jar"
IMG="eclipse-temurin:21-jre"

# 検証対象の.alsファイル（テストファイルを除く）
ALLOY_FILES=(
  "$WORKDIR/boundary.als"
  "$WORKDIR/embedding.als"
  "$WORKDIR/embedding_design_comparison_small.als"
  # embedding_design_comparison.als は大きすぎるため小さい版を使用
)

mkdir -p "$CACHE"

if [[ ! -f $JAR ]]; then
  echo "[Alloy] downloading org.alloytools.alloy.dist.jar" >&2
  curl -fsSL -o "$JAR" https://github.com/AlloyTools/org.alloytools.alloy/releases/download/v6.0.0/org.alloytools.alloy.dist.jar
fi

run_alloy_file() {
  local file="$1"
  local filename=$(basename "$file")

  if [[ ! -f "$file" ]]; then
    echo "[Alloy] SKIP: $filename (not found)" >&2
    return 0
  fi

  echo "[Alloy] checking: $filename"

  if command -v java >/dev/null 2>&1; then
    java -cp "$JAR" edu.mit.csail.sdg.alloy4whole.SimpleCLI "$file"
  else
    docker run --rm \
      -v "$WORKDIR:/work" \
      -v "$CACHE:/cache" \
      "$IMG" sh -c "java -cp /cache/alloy.jar edu.mit.csail.sdg.alloy4whole.SimpleCLI /work/$filename"
  fi
}

# 全ファイルを検証
failed=0
for file in "${ALLOY_FILES[@]}"; do
  if ! run_alloy_file "$file"; then
    failed=1
  fi
done

if [[ $failed -ne 0 ]]; then
  echo "[Alloy] Some checks failed" >&2
  exit 1
fi

echo "[Alloy] All checks passed"
