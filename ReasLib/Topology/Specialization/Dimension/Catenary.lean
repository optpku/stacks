module

public import ReasLib.Topology.Catenary
public import ReasLib.Topology.IrreducibleCloseds.Soberification.Basic
public import ReasLib.Topology.Noetherian.Basic
public import ReasLib.Topology.Specialization.Dimension
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Catenarity from Dimension Functions

This module connects a dimension function on a quasi-sober space to the
catenary interval API on irreducible closed subsets.
-/

@[expose] public section

universe u

open TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

namespace IsDimensionFunction

variable [QuasiSober X] {δ : X → ℤ}

/-- A dimension function on a quasi-sober space induces a catenary-space structure. -/
@[stacks 02IA "catenarity from a dimension function"]
theorem catenarySpace (hδ : IsDimensionFunction δ) : CatenarySpace X := sorry

/-- Along a specialization, a dimension function computes the relative codimension between the
corresponding irreducible point closures. -/
@[stacks 02IA "codimension formula for specialized point closures"]
theorem sub_eq_codimBetween_pointClosure (hδ : IsDimensionFunction δ)
    (x y : X) (hxy : x ⤳ y) :
    δ x - δ y =
      (ENat.toNat
        (codimBetween (toIrreducibleCloseds y) (toIrreducibleCloseds x)
          hxy.toIrreducibleCloseds_le) : ℤ) := sorry

section LocallyNoetherian

variable [LocallyNoetherianSpace X] {δ' : X → ℤ}

/-- On a locally Noetherian quasi-sober space, two dimension functions differ by a locally
constant integer-valued function. -/
theorem isLocallyConstant_sub (hδ : IsDimensionFunction δ)
    (hδ' : IsDimensionFunction δ') :
    IsLocallyConstant (δ - δ') := sorry

/-- Relative to one dimension function, an integer-valued function is a dimension function
exactly when its difference from the chosen function is locally constant. -/
theorem isDimensionFunction_iff_sub_isLocallyConstant (hδ : IsDimensionFunction δ) :
    IsDimensionFunction δ' ↔ IsLocallyConstant (δ' - δ) := sorry

/-- On a locally Noetherian quasi-sober T₀ space, two dimension functions differ by a locally
constant integer-valued function. -/
@[stacks 02IB]
theorem isLocallyConstant_sub_of_sober [T0Space X] (hδ : IsDimensionFunction δ)
    (hδ' : IsDimensionFunction δ') :
    IsLocallyConstant (δ - δ') := sorry

end LocallyNoetherian

section Sober

variable [T0Space X]

/-- A dimension function on a quasi-sober T₀ space induces a catenary-space structure. -/
@[stacks 02IA "catenarity from a dimension function"]
theorem catenarySpace_of_sober (hδ : IsDimensionFunction δ) : CatenarySpace X := sorry

/-- Along a specialization in a quasi-sober T₀ space, a dimension function computes the relative
codimension between the corresponding irreducible point closures. -/
@[stacks 02IA "codimension formula for specialized point closures"]
theorem sub_eq_codimBetween_pointClosure_of_sober (hδ : IsDimensionFunction δ)
    (x y : X) (hxy : x ⤳ y) :
    δ x - δ y =
      (ENat.toNat
        (codimBetween (toIrreducibleCloseds y) (toIrreducibleCloseds x)
          hxy.toIrreducibleCloseds_le) : ℤ) := sorry

end Sober

end IsDimensionFunction

namespace TopologicalSpace.CatenarySpace

variable [LocallyNoetherianSpace X] [QuasiSober X] [T0Space X] [CatenarySpace X]

/-- Every point of a locally Noetherian quasi-sober T₀ catenary space has an open neighbourhood
whose induced topology admits a dimension function. -/
@[stacks 02IC]
theorem exists_open_dimensionFunction (x : X) :
    ∃ U : Opens X, x ∈ U ∧ ∃ δ : U → ℤ, IsDimensionFunction δ := sorry

end TopologicalSpace.CatenarySpace

namespace TopologicalSpace

variable [LocallyNoetherianSpace X] [QuasiSober X] [T0Space X]

/-- A locally Noetherian quasi-sober T₀ space is catenary exactly when every point has an open
neighbourhood whose induced topology admits an integer-valued dimension function. -/
theorem catenarySpace_iff_locally_exists_dimensionFunction :
    CatenarySpace X ↔
      ∀ x : X, ∃ U : Opens X, x ∈ U ∧ ∃ δ : U → ℤ, IsDimensionFunction δ := sorry

end TopologicalSpace
