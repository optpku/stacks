/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Category

/-!
# Levelwise Isomorphisms of Sequential Postnikov Towers

This file defines levelwise invertibility on auxiliary objects and records the
derived row-object, identity, and composition certificates.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Tower

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D]
variable {T T' : Tower D}

/-- A tower morphism is levelwise invertible when all its auxiliary-object components are
invertible. Invertibility of the row-object components then follows from the distinguished
stage triangles. -/
@[stacks 0D8Z "levelwise isomorphism of sequential Postnikov towers"]
def Hom.IsLevelwiseIso (f : T ⟶ T') : Prop :=
  ∀ n, IsIso (f.yMap n)

namespace Hom.IsLevelwiseIso

/-- A levelwise-isomorphism certificate makes every row-object component invertible. -/
theorem xMap {f : T ⟶ T'} (hf : f.IsLevelwiseIso) (n : ℕ) :
    IsIso (f.xMap n) := sorry

/-- A levelwise-isomorphism certificate makes every auxiliary-object component invertible. -/
theorem yMap {f : T ⟶ T'} (hf : f.IsLevelwiseIso) (n : ℕ) :
    IsIso (f.yMap n) := sorry

/-- The identity morphism of a sequential Postnikov tower is levelwise invertible. -/
@[stacks 0D8Z]
theorem id (T : Tower D) : (𝟙 T : T ⟶ T).IsLevelwiseIso := sorry

/-- A composite of levelwise-invertible tower morphisms is levelwise invertible. -/
@[stacks 0D8Z]
theorem comp {T'' : Tower D} {f : T ⟶ T'} {g : T' ⟶ T''}
    (hf : f.IsLevelwiseIso) (hg : g.IsLevelwiseIso) :
    (f ≫ g).IsLevelwiseIso := sorry

end Hom.IsLevelwiseIso

end CategoryTheory.PostnikovSystem.Tower
