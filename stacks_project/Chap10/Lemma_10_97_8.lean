/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.AdicCompletion.AtPrime.TensorProduct.Pi
import StacksCheckRecall

@[expose] public section

/-!
@stack 07N9

# Lemma 10.97.8

The reusable owner is the canonical completed tensor-product map in
`AdicCompletion.AtPrime.TensorProduct.Pi`.  The chapter entry recalls the
concrete map, its coordinate formulas, and its bijectivity; an equivalence is
deliberately not chosen from the deferred bijectivity proof.
-/

open IsLocalRing
open scoped TensorProduct

universe u v

namespace AdicCompletion.AtPrime.TensorProduct

variable {R : Type u} {S : Type v}
variable [CommRing R] [CommRing S] [Algebra R S]

/- Lemma 10.97.8 (tag `07N9`): the canonical owner and its reusable coordinate API. -/
@[stacks 07N9]
#check @AdicCompletion.AtPrime.TensorProduct.Pi.map
@[stacks 07N9]
#check @AdicCompletion.AtPrime.TensorProduct.Pi.map_bijective
@[stacks 07N9]
#check @AdicCompletion.AtPrime.TensorProduct.Pi.map_one_tmul

end AdicCompletion.AtPrime.TensorProduct
