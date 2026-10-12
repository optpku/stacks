/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import ReasLib.RingTheory.AdicCompletion.Exactness.ShortComplex.Flat
import StacksCheckRecall

@[expose] public section

/-!
@stack 0315

# Surjectivity and flat-cokernel exactness for adic completion
-/

/- Lemma 10.96.1 (1) [stacks 0315]: the quotient-stage criterion for surjectivity of the
canonical map on `I`-adic completions. -/
@[stacks 0315]
#check @AdicCompletion.map_surjective_of_reduceModIdeal_surjective

/- Lemma 10.96.1 (2) [stacks 0315]: a surjective map induces a surjective map on `I`-adic
completions. -/
@[stacks 0315]
#check @AdicCompletion.map_surjective

/- Lemma 10.96.1 (3) [stacks 0315]: the canonical completed short complex of a short exact
sequence with flat cokernel is short exact. -/
@[stacks 0315]
#check @AdicCompletion.mapShortComplex_shortExact_of_flat

/- Lemma 10.96.1 (4) [stacks 0315]: the canonical comparison
`AdicCompletion I R ⊗[R] M → AdicCompletion I M` is surjective for finite `M`. -/
@[stacks 0315]
#check @AdicCompletion.ofTensorProduct_surjective_of_finite
