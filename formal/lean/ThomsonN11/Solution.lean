import Mathlib

/-!
# Thomson problem for N = 11 (solution placeholder)

This file will contain the proof of the challenge statements fixed in
`ComparatorChallenges/ThomsonN11.lean`:

* `ThomsonN11.thomson_eleven_M0` : every 11-point configuration on the unit sphere has
  Coulomb energy at least `55 / 2 = 27.5`;
* `ThomsonN11.thomson_eleven_M1` : every 11-point configuration on the unit sphere has
  Coulomb energy at least `155 / 4 = 38.75`.

Planned route (see `notes/strategy.md`): three-point semidefinite bound following the KLT
N = 8 paper (arXiv:2609.22077) and the N = 7 Lean package (references/thomson-n7-lean),
with the candidate configuration implicitly characterised as the unique solution of a
stationarity system.

Until the proof is written, this file is a placeholder: it imports Mathlib so that the package
builds, and declares nothing. `scripts/check.sh` treats it accordingly (token scan on, but the
statement comparison and axiom check expect it to be filled in by a later run).

Future structure (mirroring the N = 7 package): repeat the challenge preamble verbatim at the
top of this file, then the proof, ending with the two milestone theorems proved without any of
the forbidden tokens (see the scan in `scripts/check.sh`) and with no axioms beyond `propext`,
`Classical.choice`, `Quot.sound`.
-/
