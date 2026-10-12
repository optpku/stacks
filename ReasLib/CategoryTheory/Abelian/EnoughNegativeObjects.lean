/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Abelian.Basic

@[expose] public section

universe v u

namespace CategoryTheory

/-- An abelian category has enough negative objects when every object `M` admits
an epimorphism `N ⟶ M` from an object receiving only zero maps from `M`. -/
def HasEnoughNegativeObjects (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ M : C, ∃ (N : C) (t : N ⟶ M), Epi t ∧ ∀ g : M ⟶ N, g = 0

end CategoryTheory
