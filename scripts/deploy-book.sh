#!/usr/bin/env bash
set -euo pipefail

: "${DEPLOY_HOST:?Set DEPLOY_HOST to the server hostname.}"
: "${DEPLOY_USER:?Set DEPLOY_USER to the SSH user.}"
: "${DEPLOY_PATH:?Set DEPLOY_PATH to the remote directory.}"

DEPLOY_PORT="${DEPLOY_PORT:-22}"
BOOK_OUTPUT="${BOOK_OUTPUT:-_out/book/html-multi/}"

rm -rf _out/book
lake exe generate-book --output _out/book
rsync -az --delete -e "ssh -p ${DEPLOY_PORT}" \
  "${BOOK_OUTPUT}" \
  "${DEPLOY_USER}@${DEPLOY_HOST}:${DEPLOY_PATH%/}/"
