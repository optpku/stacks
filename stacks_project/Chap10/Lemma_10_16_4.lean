module

public import Mathlib.RingTheory.OrzechProperty
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.16.4

@stack 05G8
-/

-- Declarations for this item will be appended below by the statement pipeline.


universe u v

section

variable {R : Type u} {M : Type v} [Semiring R] [OrzechProperty R]
variable [AddCommMonoid M] [Module R M] [Module.Finite R M]

/- Lemma 10.16.4: for a commutative ring `R`, any surjective endomorphism of a finite
`R`-module is bijective. Mathlib states this canonically over any semiring satisfying
`OrzechProperty`; the Stacks-project commutative-ring case is recovered via
`CommRing.orzechProperty`. -/
@[stacks 05G8]
#check @OrzechProperty.bijective_of_surjective_endomorphism

end
