#!/bin/bash

#run docker solver on file
docker run -v $(realpath $1):$(realpath $1) xnf_cdcl_solver:0.1 $(realpath $1) ${@:2}
