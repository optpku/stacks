/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Fibered.CategoryHomology.AdjointFactorization.DeltaFunctor
public import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projective computation of comparison-index homology

This leaf isolates the projective-resolution realization of the resolution-independent
comparison-index delta functor.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v w z

namespace CategoryTheory.FiberedCategoryOver.FiberHomology.AdjointFactorization

variable {B : Type u} [Category.{v} B]
variable {X Y : FiberedCategoryOver.{u, v, w, w} B}
variable (g : X ⟶ Y)
variable (J : GrothendieckTopology Y.total)
variable (K : GrothendieckTopology X.total)
variable [Functor.IsContinuous (toFunctor g) K J]
variable [HasSheafify K AddCommGrpCat.{max w z}]
variable [HasSheafify J AddCommGrpCat.{max w z}]
variable [HasProjectiveResolutions (Sheaf K AddCommGrpCat.{max w z})]

/-- With projective resolutions, left-derived lower shriek is represented by the
comparison-index Bar-homology functor. -/
@[stacks 08PK "projective comparison for derived lower shriek"]
theorem leftDerived_isomorphic (n : ℕ) :
    IsIsomorphic
      (((toFunctor g).sheafPullback AddCommGrpCat.{max w z} K J).leftDerived n)
      (sheafOfSheafFunctor.{u, v, w, z} g J K n) := sorry

/-- Objectwise readout of the projective comparison for derived lower shriek. -/
@[stacks 08PK "projective comparison for derived lower shriek on an object"]
theorem leftDerived_obj_isomorphic
    (F : Sheaf K AddCommGrpCat.{max w z}) (n : ℕ) :
    IsIsomorphic
      ((((toFunctor g).sheafPullback AddCommGrpCat.{max w z} K J).leftDerived n).obj F)
      (sheafOfSheaf.{u, v, w, z} g J K F n) := sorry

end CategoryTheory.FiberedCategoryOver.FiberHomology.AdjointFactorization
