/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Sequential Inverse Systems

A sequential inverse system in a category `A` is a functor `ℕᵒᵖ ⥤ A`, i.e. a tower of
morphisms `⋯ → X₃ → X₂ → X₁ → X₀`.

This module provides the basic vocabulary (transition maps, shift, stagewise coproduct) used
by downstream chapters for the Mittag-Leffler condition and pro-objects.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CategoryTheory

/-- A sequential inverse system in `A` is a functor `ℕᵒᵖ ⥤ A`. -/
@[stacks 08TC "sequential inverse systems"]
abbrev SequentialInverseSystem (A : Type u) [Category.{v} A] := ℕᵒᵖ ⥤ A

namespace SequentialInverseSystem

variable {A : Type u} [Category.{v} A]

/-- The family of objects underlying a sequential inverse system. -/
@[stacks 08TC "underlying family of a sequential inverse system"]
abbrev family (F : SequentialInverseSystem A) : ℕ → A :=
  fun n ↦ F.obj (op n)

/-- The transition morphism `F(j) ⟶ F(i)` for `i ≤ j`. -/
abbrev transitionMap (F : SequentialInverseSystem A) {i j : ℕ} (hij : i ≤ j) :
    F.obj (op j) ⟶ F.obj (op i) :=
  F.map (homOfLE hij).op

/-- Transition morphisms compose through every intermediate stage. -/
theorem transitionMap_comp (F : SequentialInverseSystem A) {i j k : ℕ}
    (hij : i ≤ j) (hjk : j ≤ k) :
    F.transitionMap (Nat.le_trans hij hjk) = F.transitionMap hjk ≫ F.transitionMap hij := sorry

/-- The transition map attached to a reflexive inequality is the identity. -/
@[simp]
theorem transitionMap_refl (F : SequentialInverseSystem A) (i : ℕ) :
    F.transitionMap (le_refl i) = 𝟙 (F.obj (op i)) := sorry

/-- The successor transition morphism `F(n+1) ⟶ F(n)`. -/
abbrev stepMap (F : SequentialInverseSystem A) (n : ℕ) :
    F.obj (op (n + 1)) ⟶ F.obj (op n) :=
  F.transitionMap (Nat.le_add_right n 1)

/-- A transition map factors through its final successor transition. -/
theorem transitionMap_succ_factor (F : SequentialInverseSystem A) {i k : ℕ} (hik : i ≤ k) :
    F.transitionMap (Nat.le_succ_of_le hik) = F.stepMap k ≫ F.transitionMap hik := sorry

/-- The functor which reindexes a sequential inverse system by the tail beginning at `n`. -/
def tailFunctor (n : ℕ) : ℕᵒᵖ ⥤ ℕᵒᵖ :=
  ({ toFun := fun i ↦ n + i
     monotone' := fun _ _ hij ↦ Nat.add_le_add_left hij n } : ℕ →o ℕ).toFunctor.op

/-- The `i`th object of the tail reindexing functor is the original index `n + i`. -/
@[simp]
theorem tailFunctor_obj (n : ℕ) (i : ℕᵒᵖ) :
    (tailFunctor n).obj i = op (n + i.unop) := sorry

/-- The tail of a sequential inverse system, shifted by `n`. -/
abbrev shift (F : SequentialInverseSystem A) (n : ℕ) : SequentialInverseSystem A :=
  tailFunctor n ⋙ F

/-- Evaluating a sequential inverse system shifted by `n` at stage `i` gives its original
stage `n + i`. -/
@[simp] theorem shift_obj (F : SequentialInverseSystem A) (n i : ℕ) :
    (F.shift n).obj (op i) = F.obj (op (n + i)) :=
  rfl

/-- The transition map from stage `j` to stage `i` after shifting by `n` is the original
transition map from `n + j` to `n + i`. -/
@[simp] theorem shift_transitionMap (F : SequentialInverseSystem A) (n : ℕ) {i j : ℕ}
    (hij : i ≤ j) :
    (F.shift n).transitionMap hij = F.transitionMap (Nat.add_le_add_left hij n) :=
  rfl

/-- Shifting by zero leaves a sequential inverse system unchanged. -/
@[simp]
theorem shift_zero (F : SequentialInverseSystem A) :
    F.shift 0 = F := sorry

/-- Two successive shifts compose by adding their offsets. -/
theorem shift_shift (F : SequentialInverseSystem A) (m n : ℕ) :
    (F.shift m).shift n = F.shift (m + n) := sorry

end SequentialInverseSystem

variable {A : Type u} [Category.{v} A]

/-- Shift a natural transformation of sequential inverse systems by whiskering with the tail
reindexing functor. -/
def NatTrans.shift {F G : SequentialInverseSystem A} (α : F ⟶ G) (n : ℕ) :
    F.shift n ⟶ G.shift n :=
  Functor.whiskerLeft (SequentialInverseSystem.tailFunctor n) α

/-- The component of a shifted natural transformation of sequential inverse systems is its
component at the corresponding original tail stage. -/
@[simp]
theorem SequentialInverseSystem.shiftNatTrans_app {F G : SequentialInverseSystem A}
    (α : F ⟶ G) (n : ℕ) (i : ℕᵒᵖ) :
    (α.shift n).app i = α.app (op (n + i.unop)) := sorry

end CategoryTheory
