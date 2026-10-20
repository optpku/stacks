/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.CategoryTheory.ObjectProperty.Basic
public import ReasLib.CategoryTheory.Bicategory.Equivalence.Calculus.Composition

/-!
# Equivalence closure of bicategorical object properties

This module gives the bicategorical analogue of `ObjectProperty.isoClosure`:
closure under equivalence, its universal property, and the corresponding
transport typeclass.
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Bicategory
open scoped Bicategory

namespace ObjectProperty

variable {D : Type u} [Bicategory.{w, v} D]

/-- An object property on a bicategory is closed under equivalences when equivalent objects
satisfy it simultaneously. For the associated full subbicategory this is precisely repleteness. -/
@[stacks 0040 "object property closed under bicategorical equivalences"]
class IsClosedUnderEquivalences (P : ObjectProperty D) : Prop where
  /-- Transport the object property across a bicategorical equivalence. -/
  of_equivalence {X Y : D} (e : X ≌ Y) (hX : P X) : P Y

/-- Transport an equivalence-closed object property across a bicategorical equivalence. -/
theorem prop_of_equivalence (P : ObjectProperty D) [P.IsClosedUnderEquivalences]
    {X Y : D} (e : X ≌ Y) (hX : P X) : P Y := sorry
/- Proof strategy: apply `IsClosedUnderEquivalences.of_equivalence` directly. -/

/-- Equivalent objects simultaneously satisfy an equivalence-closed object property. -/
theorem prop_iff_of_equivalence (P : ObjectProperty D) [P.IsClosedUnderEquivalences]
    {X Y : D} (e : X ≌ Y) : P X ↔ P Y := sorry
/- Proof strategy: use `prop_of_equivalence P e` in the forward direction and
`prop_of_equivalence P e.symm` in the reverse direction. -/

/-- The closure under bicategorical equivalences of an object property, analogous to mathlib
`ObjectProperty.isoClosure`. -/
@[stacks 0040 "closure of an object property under bicategorical equivalences"]
def equivalenceClosure (P : ObjectProperty D) : ObjectProperty D :=
  fun X ↦ ∃ (Y : D) (_ : P Y), Nonempty (X ≌ Y)

/-- Membership in `P.equivalenceClosure` is witnessed by an object satisfying `P` and an
equivalence to it. -/
theorem prop_equivalenceClosure_iff (P : ObjectProperty D) (X : D) :
    P.equivalenceClosure X ↔ ∃ (Y : D) (_ : P Y), Nonempty (X ≌ Y) := sorry
/- Proof strategy: unfold `equivalenceClosure`; both sides are definitionally identical. -/

/-- Every object satisfying `P` belongs to its equivalence closure. -/
theorem le_equivalenceClosure (P : ObjectProperty D) : P ≤ P.equivalenceClosure := sorry
/- Proof strategy: use the object itself and `Bicategory.Equivalence.id`. -/

/-- Equivalence closure preserves nonemptiness of an object property. -/
instance equivalenceClosure.nonempty (P : ObjectProperty D) [P.Nonempty] :
    P.equivalenceClosure.Nonempty := sorry

/-- An object satisfying `P` remains in its equivalence closure after transport across an
equivalence. -/
theorem prop_equivalenceClosure {P : ObjectProperty D} {X Y : D}
    (hX : P X) (e : X ≌ Y) : P.equivalenceClosure Y := sorry
/- Proof strategy: use `X`, `hX`, and the reversed equivalence `e.symm`. -/

/-- Equivalence closure is monotone with respect to implication of object properties. -/
theorem monotone_equivalenceClosure {P Q : ObjectProperty D} (h : P ≤ Q) :
    P.equivalenceClosure ≤ Q.equivalenceClosure := sorry
/- Proof strategy: retain the witnessing object and equivalence, and transport its property
along `h`. -/

/-- The equivalence closure of any object property is closed under bicategorical equivalences. -/
instance equivalenceClosure.isClosedUnderEquivalences (P : ObjectProperty D) :
    P.equivalenceClosure.IsClosedUnderEquivalences := sorry
/- Proof strategy: if `X ≌ Z` witnesses membership of `X` and `e : X ≌ Y`, use
`e.symm.trans` followed by the original equivalence to witness membership of `Y`. -/

/-- An equivalence-closed object property is fixed by equivalence closure. -/
theorem equivalenceClosure_eq_self (P : ObjectProperty D) [P.IsClosedUnderEquivalences] :
    P.equivalenceClosure = P := sorry
/- Proof strategy: use `le_antisymm`; transport the witness property back across its equivalence,
and use `le_equivalenceClosure` for the reverse inclusion. -/

/-- `P.equivalenceClosure` is the least equivalence-closed object property containing `P`. -/
theorem equivalenceClosure_le_iff (P Q : ObjectProperty D) [Q.IsClosedUnderEquivalences] :
    P.equivalenceClosure ≤ Q ↔ P ≤ Q := sorry
/- Proof strategy: one direction factors through `P.le_equivalenceClosure`; for the other, apply
monotonicity and `Q.equivalenceClosure_eq_self`. -/

/-- An object property is closed under bicategorical equivalences exactly when it is fixed by
equivalence closure. -/
theorem IsClosedUnderEquivalences.iff_equivalenceClosure_eq_self (P : ObjectProperty D) :
    P.IsClosedUnderEquivalences ↔ P.equivalenceClosure = P := sorry
/- Proof strategy: use `equivalenceClosure_eq_self` forward; conversely rewrite by the equality
and use the canonical closure instance. -/

end ObjectProperty

end CategoryTheory
