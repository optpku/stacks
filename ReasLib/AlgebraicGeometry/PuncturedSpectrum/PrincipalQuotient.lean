/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.PuncturedSpectrum
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Restriction
public import ReasLib.AlgebraicGeometry.Scheme.Spec.IdealSubobject
public import ReasLib.RingTheory.Ideal.Principal
public import ReasLib.RingTheory.LocalRing.Quotient
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

@[expose] public section

open CategoryTheory
open AlgebraicGeometry IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- The composite of the punctured-spectrum inclusion of `A ⧸ (f)` with the affine
quotient map factors through the punctured-spectrum inclusion of `A`. -/
theorem principalQuotient_range_le (f : maximalIdeal A) :
    Set.range
        ((@puncturedOpen (A ⧸ principalIdeal (f : A)) _ (quotientSpanSingleton f)).ι ≫
          Spec.map
            (CommRingCat.ofHom (Ideal.Quotient.mk (principalIdeal (f : A))))) ⊆
      Set.range (puncturedOpen A).ι := sorry

/-- The canonical morphism from the punctured spectrum of `A ⧸ (f)` to the
punctured spectrum of `A` induced by quotienting by `f`. -/
def principalQuotientMap (f : maximalIdeal A) :
    @scheme (A ⧸ principalIdeal (f : A)) _ (quotientSpanSingleton f) ⟶ scheme A :=
  IsOpenImmersion.lift (puncturedOpen A).ι
    ((@puncturedOpen (A ⧸ principalIdeal (f : A)) _ (quotientSpanSingleton f)).ι ≫
      Spec.map
        (CommRingCat.ofHom (Ideal.Quotient.mk (principalIdeal (f : A)))))
    (principalQuotient_range_le f)

/-- The canonical morphism from the punctured spectrum of `A ⧸ (f)` to the
punctured spectrum of `A` agrees with the affine quotient map after composing
with the open-subscheme inclusions. -/
theorem principalQuotientMap_comp_ι (f : maximalIdeal A) :
    principalQuotientMap f ≫ (puncturedOpen A).ι =
      (@puncturedOpen (A ⧸ principalIdeal (f : A)) _ (quotientSpanSingleton f)).ι ≫
        Spec.map
          (CommRingCat.ofHom (Ideal.Quotient.mk (principalIdeal (f : A)))) := sorry

/-- Quotienting a local ring by a principal element and removing the closed
point gives a closed immersion of punctured spectra. -/
instance principalQuotientMap_isClosedImmersion (f : maximalIdeal A) :
    IsClosedImmersion (principalQuotientMap f) := sorry

/-- Restriction of finite étale covers along the principal quotient is faithful
when every minimal component away from `f` has quotient dimension at least two. -/
instance finiteEtaleBaseChange_faithful_of_minimalPrimeDim
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : maximalIdeal A)
    [Fact (∀ p : PrimeSpectrum A, p.asIdeal ∈ minimalPrimes A →
        (f : A) ∉ p.asIdeal →
          (2 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal))] :
    (Scheme.finiteEtaleBaseChange (principalQuotientMap f)).Faithful := sorry

/-- Restriction of finite étale covers along the principal quotient is faithful
when every connected component of the punctured spectrum meets the quotient
punctured spectrum. -/
instance finiteEtaleBaseChange_faithful_of_meetsConnectedComponents
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : maximalIdeal A)
    [Fact (∀ x : scheme A,
        ∃ y : @scheme (A ⧸ principalIdeal (f : A)) _ (quotientSpanSingleton f),
          principalQuotientMap f y ∈ connectedComponent x)] :
    (Scheme.finiteEtaleBaseChange (principalQuotientMap f)).Faithful := sorry

end AlgebraicGeometry.PuncturedSpectrum
