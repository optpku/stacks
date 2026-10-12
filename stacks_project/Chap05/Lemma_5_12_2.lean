/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Spectral.Hom
import StacksCheckRecall

@[expose] public section

/- Lemma 5.12.2: a composition of quasi-compact maps is quasi-compact. Via
Definition 5.12.1, the Stacks quasi-compact-map notion is the canonical mathlib predicate
`IsSpectralMap`, and this is exactly `IsSpectralMap.comp`. -/
@[stacks 005B "composition of quasi-compact maps"]
#check IsSpectralMap.comp
