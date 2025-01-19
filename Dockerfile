#dockerfile for solver
FROM debian:bullseye-slim
COPY . /xorricane
RUN apt update && apt install --assume-yes --no-install-recommends build-essential cmake pkg-config libboost-all-dev libjemalloc-dev git ca-certificates libtool && cd xorricane && cmake . && make xorricane
ENTRYPOINT [ "xorricane/xorricane" ]

#
# build image with
#   docker build -t xorricane:0.1 .
# solve instance at path/fname with
#   docker run -v path/fname:path/fname xorricane:0.1 path/fname [args]
# or use docker_solve.sh
#
