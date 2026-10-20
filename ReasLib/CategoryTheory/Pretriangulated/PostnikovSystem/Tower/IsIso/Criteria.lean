/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.IsIso.Inverse
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.IsIso.Triangle

/-!
# Categorical Isomorphism Criteria for Sequential Postnikov Towers

This file relates categorical invertibility to row, auxiliary, and levelwise
component invertibility and exposes the canonical component instances.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Tower

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D]
variable {T T' : Tower D}

/-- Every row-object component of an invertible tower morphism is invertible. -/
@[stacks 0D8Z]
instance xMapIsIso (f : T ⟶ T') [IsIso f] (n : ℕ) : IsIso (f.xMap n) := sorry

/-- Every auxiliary-object component of an invertible tower morphism is invertible. -/
@[stacks 0D8Z]
instance yMapIsIso (f : T ⟶ T') [IsIso f] (n : ℕ) : IsIso (f.yMap n) := sorry

/-- A morphism of sequential Postnikov towers is invertible exactly when all its row-object and
auxiliary-object components are invertible. -/
@[stacks 0D8Z "componentwise criterion for sequential Postnikov-tower isomorphisms"]
theorem isIso_iff (f : T ⟶ T') :
    IsIso f ↔ (∀ n, IsIso (f.xMap n)) ∧ ∀ n, IsIso (f.yMap n) := sorry

/-- A tower morphism is invertible exactly when all its auxiliary-object components are
invertible. -/
@[stacks 0D8Z "levelwise criterion for sequential Postnikov-tower isomorphisms"]
theorem isIso_iff_levelwise (f : T ⟶ T') :
    IsIso f ↔ f.IsLevelwiseIso := sorry

/-- An invertible tower morphism is levelwise invertible. -/
@[stacks 0D8Z]
theorem Hom.IsLevelwiseIso.ofIsIso (f : T ⟶ T') [IsIso f] :
    f.IsLevelwiseIso := sorry

/-- The induced morphism between any pair of stage triangles is invertible. -/
@[stacks 0D8Z]
instance triangleMorphismIsIso (f : T ⟶ T') [IsIso f] (n : ℕ) :
    IsIso (Hom.triangleMorphism f n) := sorry

end CategoryTheory.PostnikovSystem.Tower
