#dockerfile to build the solver and run benchmarks on it
FROM debian:bullseye-slim
COPY . /xnf_cdcl_solver
RUN apt update && apt install --assume-yes --no-install-recommends build-essential cmake pkg-config libm4ri-dev libboost-all-dev libjemalloc-dev && cd xnf_cdcl_solver && cmake . && make xnf_cdcl_solver
ENTRYPOINT [ "xnf_cdcl_solver/xnf_cdcl_solver" ]

# build image with
#   docker build -t xnf_cdcl_solver:0.1 .
# solve instance at path/fname with
#   docker run -v path/fname:path/fname 2xnf_solver_docker path/fname [args]
# or use docker_solve.sh
# 
