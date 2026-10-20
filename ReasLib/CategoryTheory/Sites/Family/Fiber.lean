/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Sites.Family

/-!
# Fibers of morphisms of fixed-target families

This module gives the subfamily of source components mapping to one fixed target component.
-/

@[expose] public section

universe w₂ w₁ v u

namespace CategoryTheory.SemiRepresentableFamily.Over.Hom

variable {C : Type u} [Category.{v} C] {U : C}
variable { 𝒰 : SemiRepresentableFamily.Over.{w₁} U}
variable { 𝒱 : SemiRepresentableFamily.Over.{w₂} U}

/-- The family over the `j`-th target component consisting of the source components whose
indices map to `j`. -/
def fiber (φ : Hom 𝒰 𝒱) (j : 𝒱.index) :
    SemiRepresentableFamily.Over.{w₁} (𝒱.obj j).left where
  index := { i : 𝒰.index // φ.α i = j }
  obj := fun ⟨i, h⟩ ↦ h ▸ CategoryTheory.Over.mk (φ.f i).left

/-- The source object of a member of `φ.fiber j` is the corresponding source-family
component. -/
theorem fiber_obj_left (φ : Hom 𝒰 𝒱) (j : 𝒱.index) (i : (φ.fiber j).index) :
    ((φ.fiber j).obj i).left = (𝒰.obj i.1).left := sorry

/-- The structure arrow of a member of `φ.fiber j` is its component arrow followed by
transport to the chosen target component. -/
theorem fiber_obj_hom (φ : Hom 𝒰 𝒱) (j : 𝒱.index) (i : (φ.fiber j).index) :
    ((φ.fiber j).obj i).hom =
      eqToHom (fiber_obj_left φ j i) ≫ (φ.f i.1).left ≫
        eqToHom (congrArg (fun k ↦ (𝒱.obj k).left) i.2) := sorry

end CategoryTheory.SemiRepresentableFamily.Over.Hom
