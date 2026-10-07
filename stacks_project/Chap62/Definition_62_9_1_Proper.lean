module

public import stacks_project.Chap62.Lemma_62_9_2_Proper
public import stacks_project.Chap62.Definition_62_6_1_Specialization

/-!
# Proper relative cycles

This file names the additive group `c(X/S, r)` of proper relative `r`-cycles
on a locally finite type morphism `f : X ⟶ S` from a locally Noetherian
scheme.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f]
variable (r : ℕ)

/-- The additive group `c(X/S, r)` of proper relative `r`-cycles on `X / S`:
the relative `r`-cycles whose support is contained in a closed subset proper
over `S`. -/
def proper : AddSubgroup (Family f r) where
  carrier := {α | IsRelative α ∧ Scheme.Hom.CyclesOnFibers.Proper α}
  zero_mem' := sorry
  add_mem' := sorry
  neg_mem' := sorry

/-- Membership in `c(X/S, r)` is the conjunction of the relative-cycle
condition and properness of the family of fibre cycles. -/
theorem mem_proper (α : Family f r) :
    α ∈ proper f r ↔ IsRelative α ∧ Scheme.Hom.CyclesOnFibers.Proper α :=
  sorry

/-- A family lies in `c(X/S, r)` if and only if it is a relative `r`-cycle and
its support is contained in some closed subset proper over `S`. -/
theorem mem_proper_iff (α : Family f r) :
    α ∈ proper f r ↔
      IsRelative α ∧
        ∃ W : TopologicalSpace.Closeds X,
          Scheme.Hom.CyclesOnFibers.support α ⊆ W ∧ ClosedSubset.IsProperOver f W :=
  sorry

/-- Proper relative `r`-cycles form a subgroup of the group `z(X/S, r)` of all
relative `r`-cycles. -/
theorem proper_le_group : proper f r ≤ group f r := sorry

/-- A family lies in `c(X/S, r)` if and only if it is a relative `r`-cycle and
the closure of its support is proper over `S`. -/
theorem mem_proper_iff_closure (α : Family f r) :
    α ∈ proper f r ↔
      IsRelative α ∧
        ClosedSubset.IsProperOver f
          (TopologicalSpace.Closeds.closure (Scheme.Hom.CyclesOnFibers.support α)) :=
  sorry

end AlgebraicGeometry.RelativeCycle
