module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Curve.SemistableReduction.Bound
public import ReasLib.AlgebraicGeometry.Curve.SemistableReduction.Model

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Curve

/-- A smooth projective curve over the fraction field of a discrete
valuation ring, with only constant global functions, has semistable reduction after a finite
separable field extension at every maximal branch of the integral closure. -/
theorem existsSemistableReductionAfterFiniteSeparableExtension
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom] [IsProper C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom)) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
      (_ : IsScalarTower R K K') (_ : FiniteDimensional K K')
      (_ : Algebra.IsSeparable K K'),
      Scheme.Hom.hasSemistableReductionAtMaximal R K K'
        (FieldExtension.Over.baseChange K K' C) := sorry

/-- In genus zero, a separable quadratic extension identifies the
base-changed curve with the projective line and with the generic fibre of the canonical
smooth projective line over the integral closure, and gives semistable reduction at every maximal
branch of the integral closure. -/
theorem semistableReduction_genusZero
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom] [IsProper C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (h_genus : SchemeOverField.genus C
      (AlgebraicGeometry.topologicalKrullDim_eq_one C) h_globalSections = 0) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
      (_ : IsScalarTower R K K') (_ : FiniteDimensional K K')
      (_ : Algebra.IsSeparable K K'),
      Module.finrank K K' = 2 ∧
        Nonempty (FieldExtension.Over.baseChange K K' C ≅ ProjectiveSpace.schemeOver K' 1) ∧
        (let model := ProjectiveSpace.schemeOver (integralClosure R K') 1
         Smooth model.hom ∧ Projective model.hom ∧
           Nonempty (FieldExtension.Over.baseChange K K' C ≅
             Over.mk (pullback.snd model.hom
               (Spec.map (CommRingCat.ofHom (algebraMap (integralClosure R K') K')))))) ∧
        Scheme.Hom.hasSemistableReductionAtMaximal R K K'
          (FieldExtension.Over.baseChange K K' C) := sorry

/-- In genus one, after a finite separable extension every maximal
localization of the integral closure has a semistable minimal model, and every minimal such
model has smooth genus-one special fibre or a cycle of rational curves. -/
theorem semistableReduction_genusOne
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom] [IsProper C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (h_genus : SchemeOverField.genus C
      (AlgebraicGeometry.topologicalKrullDim_eq_one C) h_globalSections = 1) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
      (_ : IsScalarTower R K K') (_ : FiniteDimensional K K')
      (_ : Algebra.IsSeparable K K'),
      ∀ m : MaximalSpectrum (integralClosure R K'),
        ∃ branch : SemistableReductionBranch R K K'
            (FieldExtension.Over.baseChange K K' C) m,
          SemistableReductionBranch.genusOneShape m branch ∧
            SemistableReductionBranch.allMinimalModelsHaveGenusOneShape m branch := sorry

/-- In genus at least two, semistable reduction is obtained after a
finite separable extension whose degree is bounded by `semistableReductionBound g`. -/
theorem semistableReduction_genusGeTwo
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom] [IsProper C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (g : ℕ)
    (h_genus : g = SchemeOverField.genus C
      (AlgebraicGeometry.topologicalKrullDim_eq_one C) h_globalSections)
    (h_g : 2 ≤ g) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
      (_ : IsScalarTower R K K') (_ : FiniteDimensional K K')
      (_ : Algebra.IsSeparable K K'),
      Scheme.Hom.hasSemistableReductionAtMaximal R K K'
          (FieldExtension.Over.baseChange K K' C) ∧
        Module.finrank K K' ≤ semistableReductionBound g := sorry

end AlgebraicGeometry.Curve
