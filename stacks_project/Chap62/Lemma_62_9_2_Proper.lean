module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.Proper
public import stacks_project.Chap62.Remark_62_5_6_Support

/-!
# Proper families of cycles on fibres

This file records the Stacks condition that the support of a family of
`r`-cycles on fibres is contained in a closed subset proper over the base.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.CyclesOnFibers

/-- A family of `r`-cycles on fibres is proper when its support is contained
in a closed subset proper over the base. -/
def Proper {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ} (α : CyclesOnFibers f r) :
    Prop :=
  ∃ W : TopologicalSpace.Closeds X,
    support α ⊆ W ∧ ClosedSubset.IsProperOver f W

/-- Properness means there is a closed subset containing the support and
proper over the base. -/
theorem proper_iff {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ}
    (α : CyclesOnFibers f r) :
    Proper α ↔
      ∃ W : TopologicalSpace.Closeds X,
        support α ⊆ W ∧ ClosedSubset.IsProperOver f W :=
  sorry

/-- A family of fibre cycles is proper as soon as some closed subset proper
over the base contains its support. -/
theorem proper_of_subset {X S : Scheme.{u}} {f : X ⟶ S} {r : ℕ}
    (α : CyclesOnFibers f r) (W : TopologicalSpace.Closeds X)
    (hsupp : support α ⊆ W) (hW : ClosedSubset.IsProperOver f W) :
    Proper α :=
  sorry

end AlgebraicGeometry.Scheme.Hom.CyclesOnFibers
