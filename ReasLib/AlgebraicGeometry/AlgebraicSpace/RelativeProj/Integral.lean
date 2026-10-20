/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Presentation

/-!
# Integrality of the degree-zero algebra

The structure map to degree zero is integral when its canonical scalar map is integral
on every affine étale chart.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Opposite
open SheafOfModules.RingedSite

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeProj

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- A graded `𝒪_X`-algebra has integral structure map to its degree-zero piece when every
affine étale chart admits a one-and-mul-preserving `Type u` section model whose canonical
degree-zero scalar map is integral. -/
def IntegralDegreeZeroAlgebra
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)) : Prop :=
  ∀ U : affineEtaleSite X,
    ∃ (A : Type u) (hA : CommRing A) (grading : ℕ → Submodule ℤ A)
      (hgraded : GradedAlgebra grading)
      (model : ∀ d : ℕ,
        (𝒜.obj (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
      (hModel : IsEtaleSectionModel 𝒜 U.obj grading model),
      (etaleBaseToZero U model hModel).IsIntegral

/-- Integrality of the structure map to degree zero is equivalent to the existence on
each affine étale chart of a one-and-mul-preserving `Type u` section model with integral
canonical degree-zero scalar map. -/
theorem integralDegreeZeroAlgebra_iff
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)) :
    IntegralDegreeZeroAlgebra 𝒜 ↔
      ∀ U : affineEtaleSite X,
        ∃ (A : Type u) (hA : CommRing A) (grading : ℕ → Submodule ℤ A)
          (hgraded : GradedAlgebra grading)
          (model : ∀ d : ℕ,
            (𝒜.obj (Int.ofNat d)).val.obj (op U.obj) ≃+ ULift.{u + 1} (grading d))
          (hModel : IsEtaleSectionModel 𝒜 U.obj grading model),
          (etaleBaseToZero U model hModel).IsIntegral :=
  Iff.rfl

end AlgebraicGeometry.AlgebraicSpace.RelativeProj
