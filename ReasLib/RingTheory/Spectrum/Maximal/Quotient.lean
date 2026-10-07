module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Maximal spectra of quotient rings

Maximal ideals pull back along a surjective ring map.  The resulting injection is the reusable
finiteness interface behind quotient-ring reductions; the quotient specialization is kept as a
small corollary rather than hiding the map in a local construction.
-/

@[expose] public section

universe u v

namespace MaximalSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- Pull back a maximal point along a surjective ring homomorphism. -/
@[stacks 03C1 "maximal-spectrum comap along a quotient map"]
def comapOfSurjective (f : R →+* S) (hf : Function.Surjective f) :
    MaximalSpectrum S → MaximalSpectrum R :=
  fun x ↦ ⟨Ideal.comap f x.asIdeal, Ideal.comap_isMaximal_of_surjective f hf⟩

/-- Pullback of maximal points along a surjective ring homomorphism is injective. -/
@[stacks 03C1 "injectivity of maximal-spectrum comap"]
theorem comap_injective_of_surjective (f : R →+* S) (hf : Function.Surjective f) :
    Function.Injective (comapOfSurjective f hf) := sorry

/-- A surjective map from a ring with finite maximal spectrum has a target with finite maximal
spectrum. -/
@[stacks 03C1 "finite maximal spectrum under a surjective quotient"]
theorem finite_of_finite_comap (f : R →+* S) (hf : Function.Surjective f)
    [Finite (MaximalSpectrum R)] :
    Finite (MaximalSpectrum S) := sorry

/-- Quotients of a ring with finite maximal spectrum again have finite maximal spectrum. -/
@[stacks 03C1 "finite maximal spectrum of an ideal quotient"]
theorem finite_quotient (I : Ideal R) [Finite (MaximalSpectrum R)] :
    Finite (MaximalSpectrum (R ⧸ I)) := sorry

end MaximalSpectrum
