module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteLocallyFree.UniformizerRoot
public import ReasLib.RingTheory.DiscreteValuationRing.Localization.ReducedQuotient
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.UniformizerRoot.Tame

open AlgebraicGeometry Ideal IsLocalRing

universe u

noncomputable section

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable (f : A) (hf : f ∈ nonZeroDivisors A)
variable [IsReduced (A ⧸ Ideal.span {f})]
variable (e : ℕ) (he : 1 ≤ e) (he_unit : IsUnit (e : A))
variable (p : Ideal A) [p.IsPrime] (hp : p ∈ (Ideal.span {f}).minimalPrimes)

/- Example 58.31.4 (Standard tamely ramified morphism) (1): at every minimal prime
over `(f)`, the localization of `A` is a discrete valuation ring in which the image of `f`
generates the maximal ideal. -/
@[stacks 0EYF]
#check (minimalPrimes.isDiscreteValuationRing_atPrime_of_reduced_quotient f hf p hp :
    ∃ h_domain : IsDomain (Localization.AtPrime p),
      @IsDiscreteValuationRing (Localization.AtPrime p) inferInstance h_domain ∧
        maximalIdeal (Localization.AtPrime p) =
          Ideal.span {algebraMap A (Localization.AtPrime p) f})

/- Example 58.31.4 (Standard tamely ramified morphism) (2): the spectrum map of the
explicit root algebra `A[x]/(x ^ e - f)` is finite locally free. -/
@[stacks 0EYF]
#check (AlgebraicGeometry.Scheme.Hom.isFiniteLocallyFree_uniformizerRoot f e he :
    IsFiniteLocallyFree
      (Spec.map (CommRingCat.ofHom
        (algebraMap A (DVR.UniformizerRoot.RootRing f e)))))

/- Example 58.31.4 (Standard tamely ramified morphism) (3): after inverting `f`, the
spectrum map of the explicit root algebra is finite etale. -/
@[stacks 0EYF]
#check (AlgebraicGeometry.Scheme.Hom.isFiniteEtale_uniformizerRoot_away f e he he_unit :
    let C := DVR.UniformizerRoot.RootRing f e
    let g := Localization.awayMap (algebraMap A C) f
    IsFinite (Spec.map (CommRingCat.ofHom g)) ∧
      Etale (Spec.map (CommRingCat.ofHom g)))

/- Example 58.31.4 (Standard tamely ramified morphism) (4): at every minimal prime
over `(f)`, the corresponding explicit root extension of the fraction field is tamely
ramified.  This is the affine codimension-one form of the source's final assertion. -/
@[stacks 0EYF]
#check (DVR.UniformizerRoot.isTamelyRamified_atMinimalPrime f hf e he he_unit p hp :
    let h_local := minimalPrimes.isDiscreteValuationRing_atPrime_of_reduced_quotient f hf p hp
    -- Local instance justification (defeq pin): use the domain proof indexing the local DVR.
    letI : IsDomain (Localization.AtPrime p) := h_local.choose
    -- Local instance justification (proof-local temporary data): derive the DVR at this prime.
    letI : IsDiscreteValuationRing (Localization.AtPrime p) := h_local.choose_spec.1
    -- Local instance justification (proof-local temporary data): derive the canonical root field.
    letI : Fact (Irreducible
        (DVR.UniformizerRoot.fractionPolynomial (algebraMap A (Localization.AtPrime p) f) e)) :=
      ⟨DVR.UniformizerRoot.fractionPolynomial_irreducible
        ((IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr h_local.choose_spec.2)
        (Nat.ne_zero_of_lt he)⟩
    @DVR.Field.IsTamelyRamified
      (Localization.AtPrime p) (FractionRing (Localization.AtPrime p))
      (DVR.UniformizerRoot.RootExtension (algebraMap A (Localization.AtPrime p) f) e)
      _ _ _ _ _ _ _ DVR.UniformizerRoot.baseAlgebra DVR.UniformizerRoot.fractionAlgebra
      (IsScalarTower.of_algebraMap_eq' rfl))
