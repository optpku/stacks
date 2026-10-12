/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.IntFamily
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Morphism.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Extension of Morphisms of Finite Postnikov Systems

The generic successor-diagonal shifted-Hom condition first transfers to the
auxiliary objects of a Postnikov system, then makes every finite-row morphism
lift to a Postnikov-system morphism.
-/

open CategoryTheory.Pretriangulated

universe v u

namespace CategoryTheory

namespace PostnikovSystem

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]

/-- Stacks 0D82, Lemma 13.41.4: successor-diagonal vanishing into a finite row transfers to the
auxiliary objects of any Postnikov system on that row. -/
@[stacks 0D82]
theorem vanishesAboveSuccessor_auxiliary
    {n : ℕ} {X X' : ComposableArrows D n} (P' : PostnikovSystem X')
    (h : ShiftedHom.vanishesAboveSuccessor X.intFamily X'.intFamily) :
    ShiftedHom.vanishesAboveSuccessor X.intFamily P'.intFamily := sorry

end

end PostnikovSystem

namespace PostnikovSystem.Morphism

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ m : ℤ, Functor.Additive (shiftFunctor D m)] [Pretriangulated D]

/-- Stacks 0D82, Lemma 13.41.4: successor-diagonal shifted-Hom vanishing lets a finite-row
morphism extend to a morphism of Postnikov systems. -/
@[stacks 0D82]
theorem nonempty_of_vanishesAboveSuccessor
    {n : ℕ} {X X' : ComposableArrows D n} (P : PostnikovSystem X) (P' : PostnikovSystem X')
    (φ : X ⟶ X') (h : ShiftedHom.vanishesAboveSuccessor X.intFamily X'.intFamily) :
    Nonempty (PostnikovSystem.Morphism P P' φ) := sorry

end

end PostnikovSystem.Morphism

end CategoryTheory
