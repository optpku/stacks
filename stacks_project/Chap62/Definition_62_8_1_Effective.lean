module

public import stacks_project.Chap62.Lemma_62_8_2_Effective
public import stacks_project.Chap62.Definition_62_6_1_Specialization

/-!
# Effective relative cycles

This file names the additive monoid `z^{eff}(X/S, r)` of effective relative
`r`-cycles on a locally finite type morphism `f : X ⟶ S` from a locally
Noetherian scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f]
variable (r : ℕ)

/-- The additive monoid `z^{eff}(X/S, r)` of effective relative `r`-cycles on
`X / S`: the relative `r`-cycles whose fibre cycles are effective. -/
def effective : AddSubmonoid (Family f r) where
  carrier := {α | IsRelative α ∧ IsEffective α}
  zero_mem' := sorry
  add_mem' := sorry

/-- Membership in `z^{eff}(X/S, r)` is the conjunction of the relative-cycle
condition and fibrewise effectiveness. -/
theorem mem_effective (α : Family f r) :
    α ∈ effective f r ↔ IsRelative α ∧ IsEffective α :=
  sorry

/-- A family lies in `z^{eff}(X/S, r)` if and only if it is a relative `r`-cycle
and every coefficient of every fibre cycle is nonnegative. -/
theorem mem_effective_iff_nonneg (α : Family f r) :
    α ∈ effective f r ↔
      IsRelative α ∧
        ∀ s : S, ∀ x : f.fiber s,
          0 ≤ CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s) x :=
  sorry

end AlgebraicGeometry.RelativeCycle
