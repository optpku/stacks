module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import ReasLib.AlgebraicGeometry.Curve.StableOfGenus
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Basic
public import stacks_project.Chap109.Definition_109_22_2_Family

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Theorem 109.24.3 (1): if `R` is a discrete valuation ring with fraction field `K` and `C`
is a smooth projective curve over `K` with `H⁰(C, 𝒪_C) = K` and genus `g ≥ 2`, then there
exists an extension of discrete valuation rings `R ⊂ R'` inducing a finite separable
extension of fraction fields `K'/K` and a stable family of genus `g` curves
`Y ⟶ Spec (R')` with `Y_{K'} ≅ C_{K'}` over `K'`. -/
@[stacks 0E98]
theorem existsStableFamilyAfterDVRExtension
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom] [IsProper C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (g : ℕ)
    (h_genus :
      SchemeOverField.genus C (topologicalKrullDim_eq_one C) h_globalSections = g)
    (hg : 2 ≤ g) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
      (_ : Algebra R R') (_ : IsExtensionOfDiscreteValuationRings R R')
      (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
      (_ : Algebra R' K') (_ : IsScalarTower R K K') (_ : IsScalarTower R R' K')
      (_ : IsFractionRing R' K') (_ : FiniteDimensional K K')
      (_ : Algebra.IsSeparable K K')
      (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of R'))
      (genericFiberIso :
        FieldExtension.Over.baseChange K K' C ≅ Over.mk
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R' K'))))),
      IsProper f ∧ IsStableFamily f ∧ IsStableFamilyOfGenus g f := sorry

/-- Theorem 109.24.3 (2): if `R` is a discrete valuation ring with fraction field `K` and `C`
is a smooth projective curve over `K` with `H⁰(C, 𝒪_C) = K` and genus `g ≥ 2`, then there
exists a finite separable extension `L / K` and a stable family of genus `g` curves
`Y ⟶ Spec (integralClosure R L)` such that `Y_L ≅ C_L` over `L`. -/
@[stacks 0E98]
theorem existsStableFamilyOverIntegralClosure
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom] [IsProper C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (g : ℕ)
    (h_genus :
      SchemeOverField.genus C (topologicalKrullDim_eq_one C) h_globalSections = g)
    (hg : 2 ≤ g) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Algebra R L)
      (_ : IsScalarTower R K L) (_ : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L)
      (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of (integralClosure R L)))
      (genericFiberIso :
        FieldExtension.Over.baseChange K L C ≅ Over.mk
          (pullback.snd f (Spec.map (CommRingCat.ofHom
            (algebraMap (integralClosure R L) L))))),
      IsProper f ∧ IsStableFamily f ∧ IsStableFamilyOfGenus g f := sorry

end AlgebraicGeometry.Scheme.Hom
