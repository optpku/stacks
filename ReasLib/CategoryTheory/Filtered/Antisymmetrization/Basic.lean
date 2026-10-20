/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.Equivalence
public import Mathlib.Order.Category.PartOrd

/-!
# Basic API for preorder antisymmetrization

This file records the order-theoretic and categorical facts needed to replace a
preorder-indexed system by its antisymmetrization. The carrier remains mathlib's
`Antisymmetrization`.
-/

@[expose] public section

universe u

namespace Antisymmetrization

variable {α : Type u} {r : α → α → Prop} [IsPreorder α r]

/-- Choosing a representative after projecting an element to the antisymmetrization preserves its
mutual-comparability class. -/
@[stacks 0CN1 "representative comparison for preorder antisymmetrization"]
theorem ofAntisymmetrization_toAntisymmetrization_rel (a : α) :
    AntisymmRel r (ofAntisymmetrization r (toAntisymmetrization r a)) a := sorry
/- Proof strategy: apply the quotient exactness criterion to
`toAntisymmetrization_ofAntisymmetrization (toAntisymmetrization r a)`. -/

/-- Antisymmetrization preserves nonemptiness. -/
@[stacks 0CN1 "nonemptiness descends to the antisymmetrized partial order"]
instance instNonempty [Nonempty α] : Nonempty (Antisymmetrization α r) := sorry
/- Proof strategy: map an inhabitant along `toAntisymmetrization r`. -/

variable {I : Type u} [Preorder I]

/-- Pairwise upper-bound directedness descends from a preorder to its antisymmetrization.
Nonemptiness remains a separate instance, as in mathlib's `IsDirectedOrder`. -/
@[stacks 0CN1 "upper-bound directedness descends to the antisymmetrized partial order"]
instance instIsDirectedOrder [IsDirectedOrder I] :
    IsDirectedOrder (Antisymmetrization I (· ≤ ·)) := sorry
/- Proof strategy: choose representatives of two quotient classes, take their common upper bound
in `I`, and project it; use `toAntisymmetrization_le_toAntisymmetrization_iff` for both bounds. -/

end Antisymmetrization

namespace CategoryTheory

variable {I : Type u} [Preorder I]

/-- The quotient functor from a preorder to its antisymmetrization is an equivalence of thin
categories. -/
@[stacks 0CN1 "quotient functor is a categorical equivalence"]
instance toAntisymmetrizationIsEquivalence :
    Functor.IsEquivalence
      (toAntisymmetrization_mono.functor : I ⥤ Antisymmetrization I (· ≤ ·)) := sorry
/- Proof strategy: order reflection makes the functor fully faithful because both categories are
thin. Every quotient class is represented by `ofAntisymmetrization`, giving essential
surjectivity; conclude with `Functor.isEquivalence_iff`. -/

end CategoryTheory
