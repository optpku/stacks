module

public import ReasLib.Algebra.Homology.DerivedCategory.Dualizing.Intrinsic
public import ReasLib.AlgebraicGeometry.PuncturedSpectrum.PrincipalQuotient
public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.Neighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Noetherian.Open
public import Mathlib.Algebra.Homology.LocalCohomology
public import Mathlib.Algebra.Regular.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
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

end AlgebraicGeometry.PuncturedSpectrum
