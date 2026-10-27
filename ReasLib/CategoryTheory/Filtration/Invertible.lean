/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.Order.RelSeries
public import ReasLib.CategoryTheory.Monoidal.Invertible

/-! # Finite filtrations with tensor-invertible quotients -/

@[expose] public section

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [HasZeroMorphisms C] [HasCokernels C]

/-- Two subobjects are related when the first is contained in the second and their cokernel
quotient is tensor-invertible. -/
def invertibleQuotientRel (E : C) (F G : Subobject E) : Prop :=
  ∃ (hFG : F ≤ G), isInvertibleObject (cokernel (Subobject.ofLE F G hFG))

variable [HasZeroObject C]

/-- An object has an invertible-quotient filtration if it admits a finite
`RelSeries` of subobjects from `⊥` to `⊤` whose successive cokernels are invertible. -/
def HasInvertibleQuotientFiltration (E : C) : Prop :=
  ∃ s : RelSeries (setOf fun p : Subobject E × Subobject E ↦ invertibleQuotientRel E p.1 p.2),
    s.head = ⊥ ∧ s.last = ⊤

/-- An object has an invertible-quotient filtration of length `r` if it admits a
`RelSeries` of that length from `⊥` to `⊤` whose successive cokernels are invertible. -/
def HasInvertibleQuotientFiltrationOfLength (r : ℕ) (E : C) : Prop :=
  ∃ s : RelSeries (setOf fun p : Subobject E × Subobject E ↦ invertibleQuotientRel E p.1 p.2),
    s.length = r ∧ s.head = ⊥ ∧ s.last = ⊤

/-- A prescribed-length invertible-quotient filtration is exactly a `RelSeries` of that
length from `⊥` to `⊤` with invertible successive cokernels. -/
theorem hasInvertibleQuotientFiltrationOfLength_iff (r : ℕ) (E : C) :
    HasInvertibleQuotientFiltrationOfLength r E ↔
      ∃ s : RelSeries (setOf fun p : Subobject E × Subobject E ↦ invertibleQuotientRel E p.1 p.2),
        s.length = r ∧ s.head = ⊥ ∧ s.last = ⊤ :=
  sorry

/-- Forgetting the length of a prescribed invertible-quotient filtration yields an
invertible-quotient filtration. -/
theorem HasInvertibleQuotientFiltrationOfLength.toHasInvertibleQuotientFiltration
    {r : ℕ} {E : C} (h : HasInvertibleQuotientFiltrationOfLength r E) :
    HasInvertibleQuotientFiltration E :=
  sorry

end CategoryTheory
