/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.Topology.Category.TopCommRingCat

/-! # Forgetting topology on sheaves of topological commutative rings -/

@[expose] public section

noncomputable section

universe u v w

namespace CategoryTheory

/-- Forget the topology on the values of a sheaf of topological commutative
rings, landing in `RingCat`. -/
def topCommRingSheafToRingSheaf {C : Type v} [Category.{w} C]
    {J : GrothendieckTopology C} (𝒪 : Sheaf J TopCommRingCat.{u}) :
    Sheaf J RingCat.{u} :=
  ⟨𝒪.obj ⋙ forget₂ TopCommRingCat CommRingCat ⋙ forget₂ CommRingCat RingCat,
    sorry⟩

/-- The underlying ring of a forgotten topological-ring sheaf at `U` is the
forgetful image of the topological-ring value. -/
theorem topCommRingSheafToRingSheaf_obj {C : Type v} [Category.{w} C]
    {J : GrothendieckTopology C} (𝒪 : Sheaf J TopCommRingCat.{u}) (U : Cᵒᵖ) :
    (topCommRingSheafToRingSheaf 𝒪).obj.obj U =
      (forget₂ TopCommRingCat CommRingCat ⋙ forget₂ CommRingCat RingCat).obj
        (𝒪.obj.obj U) := sorry

end CategoryTheory
