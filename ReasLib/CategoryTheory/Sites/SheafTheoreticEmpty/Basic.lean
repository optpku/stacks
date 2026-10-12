/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Sites.Grothendieck

/-!
# Sheaf-theoretically empty objects: basic site API

The intrinsic content of sheaf-theoretic emptiness is that the bottom sieve is
covering.  Sheafification and representable characterizations live in the
parent bridge module.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]

/-- An object is sheaf-theoretically empty exactly when its bottom sieve is a
cover. -/
@[stacks 04B5]
def IsSheafTheoreticallyEmpty (J : GrothendieckTopology C) (U : C) : Prop :=
  (⊥ : Sieve U) ∈ J U

namespace IsSheafTheoreticallyEmpty

/-- A pullback of a sheaf-theoretically empty object is sheaf-theoretically
empty. -/
theorem of_arrow
    {J : GrothendieckTopology C} {U U' : C}
    (hU : J.IsSheafTheoreticallyEmpty U) (f : U' ⟶ U) :
    J.IsSheafTheoreticallyEmpty U' := sorry

end IsSheafTheoreticallyEmpty

/-- The intrinsic bottom-sieve characterization of sheaf-theoretic
emptiness. -/
@[simp]
theorem isSheafTheoreticallyEmpty_iff_bot_mem
    (J : GrothendieckTopology C) (U : C) :
    J.IsSheafTheoreticallyEmpty U ↔ (⊥ : Sieve U) ∈ J U := sorry

end CategoryTheory.GrothendieckTopology
