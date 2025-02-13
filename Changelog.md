# Changelog
## v0.4.2.7

bug fix in warm restarts
minor improvement for bump_score(lineral)
bump_score of all vars in learnt cls

## v0.4.2.6

change FLS to only find trivial ones
linear increment of bump_mult
dynamic tier2_limit update (similar to kissat)


## v0.4.2.5

complement incomplete LGJ with basic lineral-watching on dl 0
prepare dynamic adjustments of bump_decay and LBD-based restarting bounds
LBD-values recomputed when used in conflict analysis -> promotion/demotion of clauses
use SCC+FLS inprocessing only for the first 100 IG-simplifications

## v0.4.2.4

bump utility of clauses contributing to conflict
enlarge tier0 (LBD<=3) and tier1 range (LBD<=7)

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
