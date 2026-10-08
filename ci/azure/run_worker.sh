#!/bin/bash
set -euo pipefail
cd /opt/a060957-job/source
export DEBIAN_FRONTEND=noninteractive
timeout 180 apt-get update -qq
timeout 180 apt-get install -y -qq curl git zstd ca-certificates libicu74
python3 worker.py
