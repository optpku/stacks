/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Presheaf.Basic
public import ReasLib.CategoryTheory.Sites.Presheaf.Terminal
public import Mathlib.CategoryTheory.Types.Basic

@[expose] public section

universe u v w

namespace CategoryTheory.Presheaf

variable {C : Type u} [Category.{v} C]

/-- The global sections of a presheaf are the morphisms from the terminal presheaf. -/
abbrev globalSections (F : Presheaf.{u, v, w} C) : Type (max u w) :=
  terminal.{w} C ⟶ F

/-- The value of a global section at an object, obtained by evaluating its singleton component. -/
def globalSectionsEval (F : Presheaf.{u, v, w} C) (s : globalSections F) (X : Cᵒᵖ) : F.obj X :=
  s.app X PUnit.unit

/-- Evaluated global sections are compatible with every restriction map. -/
lemma globalSectionsEval_naturality (F : Presheaf.{u, v, w} C) (s : globalSections F)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    F.map f (globalSectionsEval F s X) = globalSectionsEval F s Y := by
  change F.map f (s.app X PUnit.unit) = s.app Y PUnit.unit
  have hmap : (terminal.{w} C).map f = 𝟙 _ := rfl
  have hunit : ((𝟙 ((terminal.{w} C).obj X)) : (terminal.{w} C).obj X ⟶
      (terminal.{w} C).obj X) PUnit.unit = PUnit.unit := rfl
  have hn := (s.naturality_apply f (PUnit.unit : (terminal.{w} C).obj X)).symm
  rw [hmap] at hn
  convert hn using 1
  exact congrArg (s.app Y) hunit

end CategoryTheory.Presheaf
