/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Effective
public import ReasLib.AlgebraicGeometry.RelativeCycle

/-!
# Effective families of relative fibre cycles

This file records the fibrewise effectiveness predicate on a family of
cycles on scheme-theoretic fibres.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- A family of fibrewise cycles is effective when every fibre cycle is an effective algebraic cycle. -/
def IsEffective {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℕ}
    (α : f.FiberCycleFamily r) : Prop :=
  ∀ s : S, CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s) ∈
    AlgebraicCycle.effective (f.fiber s)

/-- Effectiveness of a fibrewise family is equivalent to nonnegativity of every fibre coefficient. -/
theorem isEffective_iff {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℕ}
    (α : f.FiberCycleFamily r) :
    IsEffective α ↔
      ∀ s : S, ∀ x : f.fiber s,
        0 ≤ CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s) x := sorry

/-- The zero family of fibrewise cycles is effective. -/
theorem isEffective_zero {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℕ} :
    IsEffective (0 : f.FiberCycleFamily r) := sorry

/-- The sum of effective fibrewise cycle families is effective. -/
theorem isEffective_add {X S : Scheme.{u}} {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℕ}
    {α β : f.FiberCycleFamily r} (hα : IsEffective α) (hβ : IsEffective β) :
    IsEffective (α + β) := sorry

/-- The additive submonoid of effective relative fibre-cycle families. -/
def effective {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] (r : ℕ) : AddSubmonoid (f.FiberCycleFamily r) where
  carrier := {α | IsRelative α ∧ IsEffective α}
  zero_mem' := ⟨isRelative_zero f r, isEffective_zero (f := f) (r := r)⟩
  add_mem' := fun hα hβ =>
    ⟨isRelative_add f r hα.1 hβ.1, isEffective_add hα.2 hβ.2⟩

/-- Membership in the additive submonoid of effective relative fibre-cycle families. -/
theorem mem_effective {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S]
    [LocallyOfFiniteType f] (r : ℕ) (α : f.FiberCycleFamily r) :
    α ∈ effective f r ↔ IsRelative α ∧ IsEffective α := sorry

/-- Membership in the effective relative-cycle submonoid is equivalent to
nonnegative coefficients on every fibre. -/
theorem mem_effective_iff_nonneg {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (r : ℕ)
    (α : f.FiberCycleFamily r) :
    α ∈ effective f r ↔
      IsRelative α ∧
        ∀ s : S, ∀ x : f.fiber s,
          0 ≤ CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s) x := sorry

end AlgebraicGeometry.RelativeCycle
