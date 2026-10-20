/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.CyclesOnFibers.Proper
public import ReasLib.AlgebraicGeometry.RelativeCycle
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily.Operations

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

namespace RelativeCycle

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f]
variable (r : ℕ)

/-- The zero family is relative and has proper support. -/
private theorem zero_mem_proper_carrier :
    IsRelative (0 : f.FiberCycleFamily r) ∧
      Scheme.Hom.CyclesOnFibers.Proper (0 : f.FiberCycleFamily r) :=
  sorry

/-- The sum of relative families with proper support is relative and has proper support. -/
private theorem add_mem_proper_carrier {α β : f.FiberCycleFamily r}
    (hα : IsRelative α ∧ Scheme.Hom.CyclesOnFibers.Proper α)
    (hβ : IsRelative β ∧ Scheme.Hom.CyclesOnFibers.Proper β) :
    IsRelative (α + β) ∧ Scheme.Hom.CyclesOnFibers.Proper (α + β) :=
  sorry

/-- The negative of a relative family with proper support is relative and has proper support. -/
private theorem neg_mem_proper_carrier {α : f.FiberCycleFamily r}
    (hα : IsRelative α ∧ Scheme.Hom.CyclesOnFibers.Proper α) :
    IsRelative (-α) ∧ Scheme.Hom.CyclesOnFibers.Proper (-α) :=
  sorry

/-- The additive group `c(X/S, r)` of proper relative `r`-cycles on `X / S`:
the relative `r`-cycles whose support is contained in a closed subset proper
over `S`. -/
def proper : AddSubgroup (f.FiberCycleFamily r) where
  carrier := {α | IsRelative α ∧ Scheme.Hom.CyclesOnFibers.Proper α}
  zero_mem' := by exact zero_mem_proper_carrier f r
  add_mem' := by exact add_mem_proper_carrier f r
  neg_mem' := by exact neg_mem_proper_carrier f r

/-- Membership in `c(X/S, r)` is the conjunction of the relative-cycle
condition and properness of the family of fibre cycles. -/
theorem mem_proper (α : f.FiberCycleFamily r) :
    α ∈ proper f r ↔ IsRelative α ∧ Scheme.Hom.CyclesOnFibers.Proper α :=
  Iff.rfl

/-- A family lies in `c(X/S, r)` if and only if it is a relative `r`-cycle and
its support is contained in some closed subset proper over `S`. -/
theorem mem_proper_iff (α : f.FiberCycleFamily r) :
    α ∈ proper f r ↔
      IsRelative α ∧
        ∃ W : TopologicalSpace.Closeds X,
          Scheme.Hom.CyclesOnFibers.support α ⊆ W ∧ ClosedSubset.IsProperOver f W :=
  Iff.rfl

/-- Proper relative `r`-cycles form a subgroup of the group `z(X/S, r)` of all
relative `r`-cycles. -/
theorem proper_le_group : proper f r ≤ group f r :=
  fun _ hα ↦ hα.1

/-- A family lies in `c(X/S, r)` if and only if it is a relative `r`-cycle and
the closure of its support is proper over `S`. -/
theorem mem_proper_iff_closure (α : f.FiberCycleFamily r) :
    α ∈ proper f r ↔
      IsRelative α ∧
        ClosedSubset.IsProperOver f
          (TopologicalSpace.Closeds.closure (Scheme.Hom.CyclesOnFibers.support α)) :=
  sorry

end RelativeCycle

/-- A proper relative cycle for a locally finite-type morphism over a locally
Noetherian scheme remains proper after arbitrary base change. -/
@[stacks 0H62]
theorem proper_baseChange {X S S' : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] (g : S' ⟶ S) (r : ℕ)
    (α : Scheme.Hom.CyclesOnFibers f r)
    (hRelative : RelativeCycle.IsRelative (r := r) α)
    (hProper : Scheme.Hom.CyclesOnFibers.Proper α) :
    Scheme.Hom.CyclesOnFibers.Proper
      (Scheme.Hom.FiberCycleFamily.baseChange (IsPullback.of_hasPullback f g) α) :=
  sorry

end AlgebraicGeometry
