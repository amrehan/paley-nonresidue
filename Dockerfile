# Clean-machine reproduction (see README).
# Build:  docker build -t paley-nonresidue .
# Run:    ./docker-reproduce.sh all     (sets the VM disk readahead, then: docker run --rm --cpus=6 --ulimit nofile=65536:65536 \
#           -v paley-nonresidue-work:/work -v paley-nonresidue-mathlib:/home/lean/.cache paley-nonresidue all)
#         (the second volume keeps Mathlib's download cache between runs)
# Needs ~210 GB of Docker disk and ~18 GB of Docker memory; on Docker Desktop use docker-reproduce.sh, which also
# applies the VM disk-readahead fix the final import needs (see NOTES.md).
FROM ubuntu:24.04
RUN apt-get update && apt-get install -y --no-install-recommends \
      curl git ca-certificates python3 \
    && rm -rf /var/lib/apt/lists/*
RUN useradd -m lean && mkdir -p /work && chown lean /work
USER lean
RUN mkdir -p /home/lean/.cache
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain none
ENV PATH=/home/lean/.elan/bin:$PATH
ENV WORK=/work
COPY --chown=lean . /repro
WORKDIR /repro
ENTRYPOINT ["/repro/reproduce.sh"]
CMD ["all"]
