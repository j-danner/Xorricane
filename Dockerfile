#dockerfile for solver
FROM debian:bullseye-slim
COPY . /xnf_cdcl_solver
RUN apt update && apt install --assume-yes --no-install-recommends build-essential cmake pkg-config libboost-all-dev libjemalloc-dev git && cd xnf_cdcl_solver && cmake . && make xnf_cdcl_solver
ENTRYPOINT [ "xnf_cdcl_solver/xnf_cdcl_solver" ]

#
# build image with
#   docker build -t xnf_cdcl_solver:0.1 .
# solve instance at path/fname with
#   docker run -v path/fname:path/fname xnf_cdcl_solver:0.1 path/fname [args]
# or use docker_solve.sh
#
