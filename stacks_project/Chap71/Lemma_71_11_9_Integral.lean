/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import stacks_project.Chap71.Lemma_71_11_10_FiniteType

/-!
# Étale-local integrality of the degree-zero algebra

On affine objects of the small étale site, the structure map `𝒪_X → 𝒜_0` is integral when
the canonical ring homomorphism `etaleBaseToZero` of a one-and-mul-preserving `Type u`
section model is an integral algebra map.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open SheafOfModules.RingedSite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- The canonical map from functions on an affine étale chart to the degree-zero piece of a
one-and-mul-preserving `Type u` section model is an integral ring homomorphism. -/
def integralBaseToZero
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (U : affineEtaleSite X) {A : Type u} [CommRing A]
    {grading : ℕ → Submodule ℤ A} [GradedAlgebra grading]
    (model : ∀ d : ℕ,
      (𝒜 (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
    (hModel : IsEtaleSectionModel 𝒜 U.obj grading model) : Prop :=
  (etaleBaseToZero U model hModel).IsIntegral

/-- `integralBaseToZero` is integrality of `etaleBaseToZero`. -/
theorem integralBaseToZero_iff
    {𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)}
    (U : affineEtaleSite X) {A : Type u} [CommRing A]
    {grading : ℕ → Submodule ℤ A} [GradedAlgebra grading]
    (model : ∀ d : ℕ,
      (𝒜 (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
    (hModel : IsEtaleSectionModel 𝒜 U.obj grading model) :
    integralBaseToZero U model hModel ↔ (etaleBaseToZero U model hModel).IsIntegral :=
  sorry

/-- A graded `𝒪_X`-algebra has integral structure map to its degree-zero piece when every affine
étale chart admits a one-and-mul-preserving `Type u` model whose `etaleBaseToZero` is integral,
equivalently the integral closure of `𝒪_X` in `𝒜_0` equals `𝒜_0` on that chart. -/
def IntegralDegreeZeroAlgebra
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)) : Prop :=
  ∀ U : affineEtaleSite X,
    ∃ (A : Type u) (hA : CommRing A) (grading : ℕ → Submodule ℤ A)
      (hgraded : GradedAlgebra grading)
      (model : ∀ d : ℕ,
        (𝒜 (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
      (hModel : @IsEtaleSectionModel S X 𝒜 U.obj A hA grading hgraded model),
      @integralBaseToZero S X 𝒜 U A hA grading hgraded model hModel

/-- Integrality of `𝒪_X → 𝒜_0` is the affine-étale existence of a one-and-mul-preserving
`Type u` model whose `etaleBaseToZero` is integral. -/
theorem integralDegreeZeroAlgebra_iff
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)) :
    IntegralDegreeZeroAlgebra 𝒜 ↔
      ∀ U : affineEtaleSite X,
        ∃ (A : Type u) (hA : CommRing A) (grading : ℕ → Submodule ℤ A)
          (hgraded : GradedAlgebra grading)
          (model : ∀ d : ℕ,
            (𝒜 (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
          (hModel : @IsEtaleSectionModel S X 𝒜 U.obj A hA grading hgraded model),
          @integralBaseToZero S X 𝒜 U A hA grading hgraded model hModel :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
