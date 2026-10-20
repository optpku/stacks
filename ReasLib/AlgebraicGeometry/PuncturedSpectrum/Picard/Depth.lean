module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Pullback
public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Intrinsic
public import ReasLib.RingTheory.Depth
public import ReasLib.RingTheory.Depth.RegularQuotient
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.Defs

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory
open scoped ENat

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/-- For a Noetherian local ring with a dualizing complex and depth at least three,
Picard pullback to a regular principal closed fiber of the punctured spectrum is
injective if every prime containing the defining element with two-dimensional
quotient has localized depth at least two. -/
theorem picardPullback_injective_of_dualizing_depth
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f)
    (h_dualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizing)
    (h_depth : (3 : ℕ∞) ≤ moduleDepth A A)
    (h_prime_depth : ∀ p : PrimeSpectrum A,
      f ∈ p.asIdeal →
        ringKrullDim (A ⧸ p.asIdeal) = (2 : WithBot ℕ∞) →
          (2 : ℕ∞) ≤
            moduleDepth (Localization.AtPrime p.asIdeal)
              (Localization.AtPrime p.asIdeal)) :
    let quotientMap :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
    let punctured := PuncturedSpectrum.puncturedOpen A
    Function.Injective (Scheme.Hom.picardPullback (quotientMap ∣_ punctured)) := sorry

/-- For a Noetherian local quotient of a regular ring, Picard pullback to a regular
principal closed fiber of the punctured spectrum is injective if the quotient has
depth at least three and every prime with one-dimensional quotient has localized
depth at least two. -/
theorem picardPullback_injective_of_regular_quotient_depth
    {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f : A) (hf_mem : f ∈ IsLocalRing.maximalIdeal A)
    (hf_regular : IsRegular f)
    (h_quotient_regular :
      ∃ (R : Type u) (_ : CommRing R) (_ : IsRegularRing R)
        (φ : R →+* A), Function.Surjective φ)
    (h_prime_depth : ∀ p : PrimeSpectrum A,
      ringKrullDim (A ⧸ p.asIdeal) = (1 : WithBot ℕ∞) →
        (2 : ℕ∞) ≤
          moduleDepth (Localization.AtPrime p.asIdeal)
            (Localization.AtPrime p.asIdeal))
    (h_depth_quotient :
      (3 : ℕ∞) ≤ moduleDepth A (A ⧸ Ideal.span ({f} : Set A))) :
    let quotientMap :=
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {f})))
    let punctured := PuncturedSpectrum.puncturedOpen A
    Function.Injective (Scheme.Hom.picardPullback (quotientMap ∣_ punctured)) := sorry

end AlgebraicGeometry.PuncturedSpectrum
