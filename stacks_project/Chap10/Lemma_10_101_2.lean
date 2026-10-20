module

public import ReasLib.RingTheory.Flatness.LocalRing
import StacksCheckRecall

/-!
# Flat, free, and projective modules over an Artinian local ring

@stack 051G
-/

@[expose] public section

open IsLocalRing

universe u v

section

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- Lemma 10.101.2: over a local ring with nilpotent maximal ideal, flatness, freeness, and
projectivity are equivalent. -/
@[stacks 051G]
#check (Module.Flat.LocalRing.tfae_free_projective (R := R) (M := M) :
  IsNilpotent (maximalIdeal R) →
    List.TFAE [Module.Flat R M, Module.Free R M, Module.Projective R M])

end
