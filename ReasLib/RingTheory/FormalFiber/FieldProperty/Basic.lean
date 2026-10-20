/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Properties of Algebras over Fields

@stack 0BIR

This file owns only the universe-polymorphic predicate type.  Formal-fiber
permanence assumptions live in the separate `FieldProperty.Laws` leaf.
-/

universe u v

set_option linter.checkUnivs false in
/-- A property of a commutative algebra over a field.  The field and algebra
may live in different universes. -/
@[stacks 0BIR "property of an algebra over a field"]
abbrev FieldAlgebraProperty : Type (max (u + 1) (v + 1)) :=
  ∀ (k : Type u) (A : Type v), [Field k] → [CommRing A] → [Algebra k A] → Prop
