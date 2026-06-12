#!/usr/bin/env bash
set -euo pipefail

rm -rf _out/book
lake exe generate-book --output _out/book
