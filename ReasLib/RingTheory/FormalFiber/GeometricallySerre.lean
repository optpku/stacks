/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.CohenMacaulay.SerreCondition
public import ReasLib.RingTheory.FormalFiber.FieldProperty

@[expose] public section

/-!
# Geometric Serre Conditions on Formal Fibers

@stack 0BIZ

The geometric `(R_n)` predicate tests Serre's condition `(R_n)` after every finite extension of
the ground field.  The predicate itself is universe-polymorphic; the formal-fiber law instance
uses the same-universe specialization required by the generic `P`-ring framework.
-/

open scoped TensorProduct

universe u v

namespace FieldAlgebraProperty

/-- Geometric Serre condition `(R_n)`, tested after every finite ground-field extension. -/
@[stacks 0BIZ "geometric Serre R field-algebra property"]
abbrev geometricallySerreR (n : ℕ) : FieldAlgebraProperty.{u, v} :=
  fun k A ↦ fun [Field k] [CommRing A] [Algebra k A] ↦
    ∀ (K : Type u) [Field K] [Algebra k K] [FiniteDimensional k K],
      SerreConditionR (K ⊗[k] A) n

/-- Geometric Serre condition `(R_n)` satisfies the five formal-fiber permanence laws. -/
@[stacks 0BIZ "geometric Serre R formal-fiber laws"]
instance geometricallySerreR.formalFiberLaws (n : ℕ) :
    (geometricallySerreR n : FieldAlgebraProperty.{u, u}).FormalFiberLaws := sorry

end FieldAlgebraProperty
