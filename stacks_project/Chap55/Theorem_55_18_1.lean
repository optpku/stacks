/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import stacks_project.Chap55.«55_18_0_1»
public import stacks_project.Chap55.Theorem_55_18_1_Model

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Curve

/-- Theorem 55.18.1 (1): a smooth projective curve over the fraction field of a discrete
valuation ring, with only constant global functions, has semistable reduction after a finite
separable field extension at every maximal branch of the integral closure. -/
@[stacks 0CDN]
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

/-- Theorem 55.18.1 (2): in genus zero, a separable quadratic extension identifies the
base-changed curve with the projective line and gives semistable reduction at every maximal
branch of the integral closure. -/
@[stacks 0CDN]
theorem semistableReduction_genusZero
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom] [IsProper C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (g : ℕ)
    (h_genus : g = SchemeOverField.genus C
      (AlgebraicGeometry.topologicalKrullDim_eq_one C) h_globalSections)
    (h_g : g = 0) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
      (_ : IsScalarTower R K K') (_ : FiniteDimensional K K')
      (_ : Algebra.IsSeparable K K'),
      Module.finrank K K' = 2 ∧
        Nonempty (FieldExtension.Over.baseChange K K' C ≅ ProjectiveSpace.schemeOver K' 1) ∧
        Scheme.Hom.hasSemistableReductionAtMaximal R K K'
          (FieldExtension.Over.baseChange K K' C) := sorry

/-- Theorem 55.18.1 (3): in genus one, after a finite separable extension every maximal
localization of the integral closure has a semistable minimal model, and every minimal such
model has smooth genus-one special fibre or a cycle of rational curves. -/
@[stacks 0CDN]
theorem semistableReduction_genusOne
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom] [IsProper C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (g : ℕ)
    (h_genus : g = SchemeOverField.genus C
      (AlgebraicGeometry.topologicalKrullDim_eq_one C) h_globalSections)
    (h_g : g = 1) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
      (_ : IsScalarTower R K K') (_ : FiniteDimensional K K')
      (_ : Algebra.IsSeparable K K'),
      ∀ m : MaximalSpectrum (integralClosure R K'),
        (∃ B : SemistableReductionBranch R K K'
            (FieldExtension.Over.baseChange K K' C) m,
          SemistableReductionBranch.genusOneShape m B) ∧
        ∀ B : SemistableReductionBranch R K K'
            (FieldExtension.Over.baseChange K K' C) m,
          SemistableReductionBranch.isMinimal m B →
            SemistableReductionBranch.genusOneShape m B := sorry

/-- Theorem 55.18.1 (4): in genus at least two, semistable reduction is obtained after a
finite separable extension whose degree is bounded by `semistableReductionBound g`. -/
@[stacks 0CDN]
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
