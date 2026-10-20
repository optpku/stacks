/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Finite-Coproduct Closure of Object Properties

This leaf owns the closure of an object property under finite coproducts and
isomorphisms.  It is independent of preadditive or triangulated structure.
-/

open CategoryTheory
open CategoryTheory.Limits

universe v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C]

/-- The closure of an object property under finite coproducts and isomorphisms. -/
@[stacks 0FX5]
abbrev additiveClosure (P : ObjectProperty C) : ObjectProperty C :=
  P.colimitsClosure fun n : ℕ ↦ Discrete (Fin n)

/-- The additive closure of an object property is closed under finite coproducts. -/
@[stacks 0FX5]
instance additiveClosure_isClosedUnderFiniteCoproducts (P : ObjectProperty C) :
    P.additiveClosure.IsClosedUnderFiniteCoproducts := sorry

/-- The additive closure is the least isomorphism- and finite-coproduct-closed
object property containing `P`. -/
@[stacks 0FX5 "universal property of additive closure"]
theorem additiveClosure_le_iff {P Q : ObjectProperty C}
    [Q.IsClosedUnderIsomorphisms] [Q.IsClosedUnderFiniteCoproducts] :
    P.additiveClosure ≤ Q ↔ P ≤ Q := by
  constructor
  · exact fun h ↦ (P.le_colimitsClosure _).trans h
  · exact fun h ↦ colimitsClosure_le h

end CategoryTheory.ObjectProperty
