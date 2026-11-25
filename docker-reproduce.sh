#!/usr/bin/env bash
# One-command Docker reproduction (macOS / Docker Desktop, or any Linux Docker host).
#   ./docker-reproduce.sh [all]     (default: all)
# Needs ~210 GB of Docker disk and ~18 GB of memory for the Docker VM (see NOTES.md).
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")"
docker build -t paley-nonresidue .

# Docker Desktop's Linux VM sets 8 MB readahead on its virtual disks. The final step imports
# ~90 GB of memory-mapped .olean files and `#print axioms` walks Alpöge's whole proof, so the
# page cache is smaller than the working set and every re-read page fault pulls in 8 MB:
# terabytes of I/O that never finish. With the Linux default of 128 KB it completes.
# This touches only the throwaway VM (reset on Docker Desktop restart), so we only do it there,
# never on a real Linux host's disks.
if [ "$(docker info --format '{{.OperatingSystem}}')" = "Docker Desktop" ]; then
  docker run --rm --privileged alpine sh -c \
    'for q in /sys/block/vd*/queue; do echo 128 > "$q/read_ahead_kb"; done'
fi

exec docker run --rm --cpus="$(docker info --format '{{.NCPU}}')" --ulimit nofile=65536:65536 \
  -v "${PALEY_VOLUME:-paley-nonresidue-work}":/work -v "${PALEY_CACHE_VOLUME:-paley-nonresidue-mathlib}":/home/lean/.cache \
  paley-nonresidue "${1:-all}"
