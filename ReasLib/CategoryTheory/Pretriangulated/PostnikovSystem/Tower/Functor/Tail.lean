/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Total.Tail.Basic
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Functor.Basic
public import ReasLib.CategoryTheory.Pretriangulated.PostnikovSystem.Tower.Morphism.Finite.Tail

/-!
# Successor Coherence for Finite Restrictions of Postnikov Towers

This leaf records compatibility of finite row and finite Postnikov-system
restriction with removal of the first stage.
-/

@[expose] public section

open CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace CategoryTheory.PostnikovSystem.Tower

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D]

/-- Successor finite-row restriction followed by row truncation is the preceding finite-row
restriction functor. -/
@[stacks 0D8Z "successor coherence of finite-row restriction"]
theorem rowFunctor_succ (n : ℕ) :
    rowFunctor D (n + 1) ⋙
        (ComposableArrows.δ₀Functor (C := D) (n := n)) =
      rowFunctor D n := sorry

/-- Successor finite-system restriction followed by total truncation is the preceding
finite-system restriction functor. -/
@[stacks 0D8Z "successor coherence of finite-system restriction"]
theorem finiteFunctor_succ (n : ℕ) :
    finiteFunctor D (n + 1) ⋙ PostnikovSystem.Total.tail D n =
      finiteFunctor D n := sorry

end CategoryTheory.PostnikovSystem.Tower
