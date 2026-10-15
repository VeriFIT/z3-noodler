# This dockerfile was created by Michal Hecko
# Eternal glory to him
#
# Build from the repository root (the build context is the checked-out sources):
#   docker build -f docker/z3-noodler.Dockerfile -t z3-noodler .
# Run (Noodler is the default string solver, no extra option is needed):
#   docker run --rm -v "$PWD":/work z3-noodler /work/file.smt2
# Mata needs <format>, i.e., GCC >= 13 (Debian bookworm ships GCC 12)
FROM debian:trixie
RUN apt-get update -y && \
    apt-get install -y --no-install-recommends git ca-certificates make cmake gcc g++ python3 && \
    rm -rf /var/lib/apt/lists/*

# Mata is fetched by CMake at the version pinned in CMakeLists.txt
COPY ./ /z3-noodler/
WORKDIR /z3-noodler/build
RUN cmake -DCMAKE_BUILD_TYPE=Release .. && make -j`nproc`
ENTRYPOINT ["/z3-noodler/build/z3"]
