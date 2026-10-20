/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.InverseImage.Squares

/-! # The actual dense-site comparison for Type u

Restriction and pointwise Ran, using the small atlas category, transport
the small-square construction back to the original algebraic-space site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PullbackFactory.TypeComparison

open Squares

variable {S : Scheme.{u}} (X : AlgebraicSpace S)

theorem dense : (inclusion X).IsDenseSubsite (topology X) (smallEtaleTopology X) :=
  SmallAtlas.denseSubsite (AtlasInput.scheme X)
    (AtlasInput.map X)
    (AtlasInput.locallySurjective X)

/-- Structured arrows from a fixed chart have small objects and morphisms. -/
theorem ran_limits (V : (smallEtaleSite X)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow V (inclusion X).op) (Type u) := by
  infer_instance

/-- The backward functor is the actual small-index Ran, not an arbitrary
inverse picked from an admitted equivalence. -/
def comparison : Sheaf (smallEtaleTopology X) (Type u) ≌ Sheaf (topology X) (Type u) := by
  -- Local instance justification (defeq pin): Use density of this explicit small-site inclusion when transporting its restriction/right-Kan sheaf adjunction.
  letI := dense X
  -- Local instance justification (defeq pin): Supply the established limits for this inclusion at X so its specified right-Kan adjunction is used.
  letI := ran_limits X
  exact ((inclusion X).sheafAdjunctionCocontinuous (Type u)
    (topology X) (smallEtaleTopology X)).toEquivalence

/-- The forward functor keeps precisely the old sections on each actual chart. -/
@[simp]
theorem comparison_obj (Q : Sheaf (smallEtaleTopology X) (Type u)) :
    ((comparison X).functor.obj Q).obj = (inclusion X).op ⋙ Q.obj := rfl

end AlgebraicGeometry.AlgebraicSpace.PullbackFactory.TypeComparison
