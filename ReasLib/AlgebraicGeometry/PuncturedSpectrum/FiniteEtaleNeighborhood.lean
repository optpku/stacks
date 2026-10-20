module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Intrinsic
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.PrincipalQuotient
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Open
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.Algebra.Regular.Defs
public import Mathlib.Order.WithBotTop
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry IsLocalRing

noncomputable section

universe u

namespace AlgebraicGeometry.PuncturedSpectrum

/-- Restriction from a colimit of finite étale categories on neighborhoods of the
principal-quotient punctured spectrum to finite étale covers of that punctured
spectrum, via the scheme-theoretic image of its canonical closed immersion. -/
def principalNeighborhoodRestriction
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : maximalIdeal A)
    (t : ColimitCocone
      (Scheme.finiteEtaleNeighborhoodDiagram (principalQuotientMap f).ker)) :
    t.cocone.pt ⥤ Scheme.FiniteEtale (scheme (A ⧸ principalIdeal (f : A))) :=
  Scheme.finiteEtaleNeighborhoodRestriction (principalQuotientMap f).ker t ⋙
    Scheme.finiteEtaleBaseChange (principalQuotientMap f).toImage

/-- For a Noetherian local ring with an intrinsic dualizing complex, complete
along an element of its maximal ideal, finite étale restriction from
neighborhoods in the punctured spectrum to the principal-quotient punctured
spectrum is fully faithful if every minimal component away from the element
has dimension at least three. -/
theorem finiteEtaleRestriction_fullyFaithful
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : maximalIdeal A)
    (h_dualizing : ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizing)
    [IsAdicComplete (Ideal.span ({(f : A)} : Set A)) A]
    (h_dim : ∀ p : PrimeSpectrum A, p.asIdeal ∈ minimalPrimes A →
      (f : A) ∉ p.asIdeal → (3 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal))
    (t : ColimitCocone
      (Scheme.finiteEtaleNeighborhoodDiagram (principalQuotientMap f).ker)) :
    Nonempty (principalNeighborhoodRestriction f t).FullyFaithful := sorry

/-- For a Noetherian local ring complete along a regular element of its maximal
ideal, finiteness of the first two local cohomology modules of the principal
quotient implies that finite étale restriction from neighborhoods in the
punctured spectrum to the quotient punctured spectrum is an equivalence. -/
instance principalNeighborhoodRestriction_isEquivalence
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : maximalIdeal A)
    [IsAdicComplete (Ideal.span {(f : A)}) A]
    [Fact (IsRegular (f : A))]
    [Module.Finite A
      ((localCohomology (maximalIdeal A) 1).obj
        (ModuleCat.of A (A ⧸ Ideal.span {(f : A)})))]
    [Module.Finite A
      ((localCohomology (maximalIdeal A) 2).obj
        (ModuleCat.of A (A ⧸ Ideal.span {(f : A)})))]
    (t : ColimitCocone
      (Scheme.finiteEtaleNeighborhoodDiagram (principalQuotientMap f).ker)) :
    Functor.IsEquivalence (principalNeighborhoodRestriction f t) := sorry

/-- For a Noetherian local ring admitting an intrinsic dualizing complex and
complete along an element of its maximal ideal, finite étale restriction from
neighborhoods in the punctured spectrum to the principal-quotient punctured
spectrum is an equivalence if either the localization away from the element
satisfies `(S₂)` and every minimal component away from it has dimension at least
four, or every prime outside the principal closed subset whose closure meets
that subset beyond the closed point has depth plus quotient dimension greater
than three. -/
instance finiteEtaleNeighborhoodRestriction_isEquivalence_of_dualizing_complete
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : IsLocalRing.maximalIdeal A)
    [h_dualizing :
      Fact (∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizing)]
    [IsAdicComplete (Ideal.span ({(f : A)} : Set A)) A]
    [h_alternative :
      Fact
        ((SerreConditionS (Localization.Away (f : A)) 2 ∧
          ∀ p : PrimeSpectrum A,
            p.asIdeal ∈ minimalPrimes A →
              (f : A) ∉ p.asIdeal →
                (4 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal)) ∨
        (∀ p : PrimeSpectrum A,
          p ∉ PrimeSpectrum.zeroLocus ({(f : A)} : Set A) →
            PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
                PrimeSpectrum.zeroLocus ({(f : A)} : Set A) ≠
              {IsLocalRing.closedPoint A} →
              (3 : EInt) <
                ((WithTop.map Int.ofNat
                  (moduleDepth (Localization.AtPrime p.asIdeal)
                    (LocalizedModule.AtPrime p.asIdeal A)) : WithTop ℤ) : EInt) +
                  WithBot.map (WithTop.map Int.ofNat)
                    (ringKrullDim (A ⧸ p.asIdeal))))]
    (t : ColimitCocone
      (Scheme.finiteEtaleNeighborhoodDiagram (principalQuotientMap f).ker)) :
    Functor.IsEquivalence (principalNeighborhoodRestriction f t) := sorry

/-- For a complete Noetherian local ring and a nonzero element of its maximal
ideal, finite étale restriction from neighborhoods in the punctured spectrum
to the principal-quotient punctured spectrum is an equivalence if localization
away from the element satisfies `(S₂)` and every irreducible component has
dimension at least four. -/
instance finiteEtaleNeighborhoodRestriction_isEquivalence_of_complete_S2_dim4
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : IsLocalRing.maximalIdeal A)
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [hf : Fact ((f : A) ≠ 0)]
    [SerreConditionS (Localization.Away (f : A)) 2]
    [hdim : Fact (∀ p : PrimeSpectrum A, p.asIdeal ∈ minimalPrimes A →
      (4 : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ p.asIdeal))]
    (t : ColimitCocone
      (Scheme.finiteEtaleNeighborhoodDiagram (principalQuotientMap f).ker)) :
    Functor.IsEquivalence (principalNeighborhoodRestriction f t) := sorry

/-- For a complete Noetherian normal local domain of dimension at least four
and a nonzero element of its maximal ideal, finite étale restriction from
neighborhoods in the punctured spectrum to the principal-quotient punctured
spectrum is an equivalence. -/
instance finiteEtaleNeighborhoodRestriction_isEquivalence_of_complete_normal_dim4
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (f : IsLocalRing.maximalIdeal A)
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    [hf : Fact ((f : A) ≠ 0)]
    [IsDomain A] [IsIntegrallyClosed A]
    [hdim : Fact ((4 : WithBot ℕ∞) ≤ ringKrullDim A)]
    (t : ColimitCocone
      (Scheme.finiteEtaleNeighborhoodDiagram (principalQuotientMap f).ker)) :
    Functor.IsEquivalence (principalNeighborhoodRestriction f t) := sorry

end AlgebraicGeometry.PuncturedSpectrum
