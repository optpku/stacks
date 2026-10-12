/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Sequence.Koszul.Monoid
import StacksCheckRecall

/-!
# Definition 15.28.1

@stack 0622
-/

@[expose] public section

/-!
# The Koszul complex of a linear form

The reusable owner is the neutral Koszul support API; this chapter entry is retained as a
source-facing recall and compatibility import.
-/

/- Definition 15.28.1 (1): the underlying graded algebra is the exterior algebra, bundled by the
canonical commutative Koszul DGA owner. -/
@[stacks 0622 "(1), exterior Koszul differential graded algebra"]
#check @KoszulComplex.commMon
#check @KoszulComplex.commMon_X
#check @KoszulComplex.X
#check @KoszulComplex.mulHom_component

/- Definition 15.28.1 (2): the differential is the unique graded derivation extending the given
linear form on degree-one generators. -/
@[stacks 0622 "(2), unique Koszul differential"]
#check @koszulDifferential
#check @KoszulDifferential.zero_oneEquiv
#check @koszulDifferential_mul
#check @CliffordAlgebra.contractLeft_unique
#check @koszulDifferentialLinearMap_apply_ιMulti_eq_sum
