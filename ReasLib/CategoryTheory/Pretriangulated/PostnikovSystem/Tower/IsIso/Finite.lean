/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Morphism.IsLevelwiseIso.Basic
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Functor.Basic
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.IsIso.Criteria

/-!
# Finite Restrictions of Isomorphisms of Sequential Postnikov Towers

Levelwise and categorical isomorphisms of towers restrict to invertible finite-row maps and
levelwise-invertible morphisms of finite Postnikov systems.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Tower

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D]
variable {T T' : Tower D}

/-- Finite-row restriction of a levelwise-invertible tower morphism is invertible. -/
@[stacks 0D8Z]
theorem Hom.IsLevelwiseIso.row {f : T ⟶ T'} (hf : f.IsLevelwiseIso) (n : ℕ) :
    IsIso (Hom.row f n) := sorry

/-- Finite restriction of a levelwise-invertible tower morphism is levelwise invertible on its
auxiliary objects. -/
@[stacks 0D8Z]
theorem Hom.IsLevelwiseIso.finite {f : T ⟶ T'} (hf : f.IsLevelwiseIso) (n : ℕ) :
    (Hom.finite f n).IsLevelwiseIso := sorry

/-- Finite-row restriction of an invertible tower morphism is invertible. -/
@[stacks 0D8Z]
instance rowIsIso (f : T ⟶ T') [IsIso f] (n : ℕ) :
    IsIso (Hom.row f n) := sorry

/-- Every auxiliary component of a finite Postnikov-system restriction is invertible. -/
@[stacks 0D8Z]
instance finiteYMapIsIso (f : T ⟶ T') [IsIso f] (n : ℕ) (i : Fin (n + 1)) :
    IsIso ((Hom.finite f n).yMap i) := sorry

/-- The finite Postnikov-system component of an invertible tower morphism is levelwise
invertible. -/
@[stacks 0D8Z]
theorem finiteIsLevelwiseIso (f : T ⟶ T') [IsIso f] (n : ℕ) :
    (Hom.finite f n).IsLevelwiseIso := sorry

end CategoryTheory.PostnikovSystem.Tower
