module

public import ReasLib.AlgebraicGeometry.AlgebraicCycle.Effective
public import stacks_project.Chap62.Lemma_62_6_6_Family

/-!
# Effective families of relative fibre cycles

This file records the fibrewise effectiveness predicate on a family of
`r`-cycles on scheme-theoretic fibres.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

/-- A family of `r`-cycles on the fibres of `f : X ⟶ S` is effective when every
fibre cycle is an effective algebraic cycle. -/
def IsEffective {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ} (α : Family f r) : Prop :=
  ∀ s : S, CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s) ∈
    AlgebraicCycle.effective (f.fiber s)

/-- Effectiveness of a fibrewise family is equivalent to nonnegativity of every
fibre coefficient. -/
theorem isEffective_iff {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ} (α : Family f r) :
    IsEffective α ↔
      ∀ s : S, ∀ x : f.fiber s,
        0 ≤ CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s) x :=
  sorry

/-- The zero family of fibrewise `r`-cycles is effective. -/
theorem isEffective_zero {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ} :
    IsEffective (0 : Family f r) := sorry

end AlgebraicGeometry.RelativeCycle
