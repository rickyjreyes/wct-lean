FROM ubuntu:24.04

ENV DEBIAN_FRONTEND=noninteractive \
    PATH=/root/.elan/bin:${PATH}

RUN apt-get update \
    && apt-get install -y --no-install-recommends \
       ca-certificates \
       curl \
       git \
       python3 \
       unzip \
       zstd \
    && rm -rf /var/lib/apt/lists/*

RUN curl --proto '=https' --tlsv1.2 -sSf \
      https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none

WORKDIR /workspace

COPY lean-toolchain lakefile.lean lake-manifest.json ./
RUN elan toolchain install "$(cat lean-toolchain)" \
    && lake update \
    && lake exe cache get

COPY . .

RUN python3 scripts/audit_formal_sources.py \
    && lake build

CMD ["lake", "build"]
