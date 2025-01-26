# Changelog

## v0.4.2.4

undo changes in 0.4.2.2 ?

## v0.4.2.3

separated restarts from clause deletion
new default clause deletion strategy: LBD-based deletion using tiers
new default restart scheduling: glue/LBD-based exponential moving average

## v0.4.2.2

change watch-lists from 'list' to 'vec'
deactivate inprocessing for propagation via CMS in LGJ

## v0.4.2.1

use CMS for LGJ elimination
fix remove_alpha and remove_equiv scheduling + mv them back into GCP
init tier info

## v0.4.2

use CMS for LGJ elimination
use M4RI in lin_sys for reduction of largish matrices (size>99)
refactor GCP & GCP_inprocess

## v0.4.1.1

(buggy) LGJ elimination
IG-preprocessing default now scc

## v0.4.0.1

xornado prepocessing (default scc_fls)
restructuring in computing 'get_reason'

## v0.3.0

bug fixes, refactoring
