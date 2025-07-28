# Tamarin
ARG GHC_VERSION=9.6.6

#----------------------------------------------------
FROM haskell:${GHC_VERSION} AS tamarin-dependencies

WORKDIR /opt/build

RUN apt-get update && apt-get install -y --no-install-recommends \
      libncurses-dev \
      zlib1g-dev \
      pkg-config \
    && rm -rf /var/lib/apt/lists/*

# Build from local directory
COPY stack.yaml tamarin-prover.cabal ./
COPY LICENSE ./
COPY lib/. ./lib/
COPY src ./src
COPY data ./data
COPY images ./images

RUN stack build --system-ghc --dependencies-only

#---------------------------------------------------
FROM haskell:${GHC_VERSION} AS tamarin-build

COPY --from=tamarin-dependencies /root/.stack /root/.stack
COPY --from=tamarin-dependencies /opt/build /opt/build

WORKDIR /opt/build

RUN stack install --system-ghc --local-bin-path /opt/build/bin

# Strip debugging symbols to reduce binary size
RUN apt-get update && \
    apt-get install -y --no-install-recommends binutils unzip && \
    strip /opt/build/bin/tamarin-prover && \
    rm -rf /var/lib/apt/lists/*

# Retrieve Maude from Git repo as APT source for bookworm is incompatible with Tamarin
RUN wget https://github.com/maude-lang/Maude/releases/download/Maude3.5/Maude-3.5-linux-x86_64.zip && unzip Maude-3.5-linux-x86_64.zip -d /opt/build/bin 

#---------------------------------------------------
FROM debian:bookworm-slim AS tamarin

# Metadata
LABEL version="1.0" \
      description="The Tamarin prover for security protocol verification" \
      org.opencontainers.image.authors="The Tamarin prover authors"

ENV PATH="/usr/local/bin:$PATH"

ENV LANG=C.UTF-8 \
    LC_ALL=C.UTF-8

RUN apt-get update \
 && DEBIAN_FRONTEND=noninteractive apt-get install -y --no-install-recommends \
      graphviz \
 && rm -rf /var/lib/apt/lists/*

COPY --from=tamarin-build /opt/build/bin /usr/local/bin

COPY etc/docker/res/entrypoint.sh /usr/local/bin/

RUN chmod 755 /usr/local/bin/entrypoint.sh

RUN useradd -ms /bin/bash tamarin
USER tamarin

WORKDIR /home/tamarin
COPY etc/docker/res/README .

EXPOSE 3001

ENTRYPOINT ["/usr/local/bin/entrypoint.sh"]
