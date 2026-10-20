/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Morphism.Basic

/-!
# Category of Sequential Postnikov Towers

Sequential Postnikov towers and their componentwise morphisms form a category.  This leaf only
packages the identity, composition, and laws owned by `PostnikovSystem.Tower.Hom`.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Tower

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- Sequential Postnikov towers and their componentwise morphisms form a category. -/
@[stacks 0D8Z "category of sequential Postnikov towers"]
instance instCategory : Category (Tower D) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.comp_assoc

/-- The row-object component of the categorical identity is an identity. -/
@[simp]
theorem id_xMap (T : Tower D) (n : ℕ) :
    (𝟙 T : T ⟶ T).xMap n = 𝟙 (T.X n) := sorry

/-- The auxiliary-object component of the categorical identity is an identity. -/
@[simp]
theorem id_yMap (T : Tower D) (n : ℕ) :
    (𝟙 T : T ⟶ T).yMap n = 𝟙 (T.Y n) := sorry

/-- Row-object components of categorical composites compose componentwise. -/
@[simp]
theorem comp_xMap {T T' T'' : Tower D} (f : T ⟶ T') (g : T' ⟶ T'')
    (n : ℕ) :
    (f ≫ g).xMap n = f.xMap n ≫ g.xMap n := sorry

/-- Auxiliary-object components of categorical composites compose componentwise. -/
@[simp]
theorem comp_yMap {T T' T'' : Tower D} (f : T ⟶ T') (g : T' ⟶ T'')
    (n : ℕ) :
    (f ≫ g).yMap n = f.yMap n ≫ g.yMap n := sorry

end CategoryTheory.PostnikovSystem.Tower
