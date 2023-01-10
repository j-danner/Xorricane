#!/bin/bash
solver="$(dirname "$0")/build/2xnf_solver"
$solver $@ -upd hfd
