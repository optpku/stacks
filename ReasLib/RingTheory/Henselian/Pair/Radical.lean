module

public import ReasLib.AlgebraicGeometry.PrimeSpectrum.Notation
public import ReasLib.RingTheory.Henselian.Pair.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pair Henselization depends only on the closed subset

The chosen Henselization ring of `(A, I)` depends, up to a unique compatible `A`-algebra
equivalence, only on the closed subset `V(I)`.

@stack 0F0L
-/

@[expose] public section

open PrimeSpectrum
open scoped PrimeSpectrum

universe u

noncomputable section

namespace RingPairCat

variable {A : Type u} [CommRing A]
variable [henselianPairInclusion.IsRightAdjoint]

/-- Lemma 15.12.6: ideals with the same zero locus have uniquely equivalent chosen
Henselization rings, compatibly with the maps from `A`. -/
@[stacks 0F0L "Lemma 15.12.6"]
theorem henselizationRing_existsUnique_algEquiv_of_zeroLocus_eq
    (I J : Ideal A) (hV : V((I : Set A)) = V((J : Set A))) :
    ∃! e : henselizationRing (pairOfIdeal I) ≃ₐ[A] henselizationRing (pairOfIdeal J),
      e.toRingHom.comp (toHenselization (pairOfIdeal I)) =
        toHenselization (pairOfIdeal J) := sorry

end RingPairCat
