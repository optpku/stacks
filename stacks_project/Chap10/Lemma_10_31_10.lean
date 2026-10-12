/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Noetherian.Orzech
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.31.10

@stack 06RN
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

/- Lemma 10.31.10 (Stacks tag `06RN`): any surjective endomorphism of a Noetherian ring is an
isomorphism. Mathlib organizes this under the owner theorem
`OrzechProperty.bijective_of_surjective_endomorphism`; the commutative Noetherian ring case is
recovered from `IsNoetherianRing.orzechProperty`, viewing a ring endomorphism `f : R →+* R` as the
linear endomorphism `f.toLinearMap` of the finite `R`-module `R`. -/
@[stacks 06RN]
#check @OrzechProperty.bijective_of_surjective_endomorphism

end
