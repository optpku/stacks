module

public import Mathlib.RingTheory.LocalRing.Module
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.78.5

@stack 00NZ
-/

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {M : Type v}
variable [CommRing R] [IsLocalRing R]
variable [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M]

/- Lemma 10.78.5: if `R` is a local ring and `M` is a finite flat `R`-module, then `M` is free.
Together with the hypothesis `Module.Finite R M`, this is exactly the statement that `M` is finite
free, and mathlib provides it as `Module.free_of_flat_of_isLocalRing`. -/
@[stacks 00NZ]
#check @Module.free_of_flat_of_isLocalRing

end
