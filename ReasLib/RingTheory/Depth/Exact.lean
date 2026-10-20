/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import ReasLib.RingTheory.Depth

/-!
# The Depth Lemma

The three symmetric depth inequalities are stated directly for a short exact
sequence of modules.  Finiteness of the middle term is a consequence of short
exactness and is therefore absent from the public parameter list.
-/

@[expose] public section

open CategoryTheory
open scoped ENat

universe u v

namespace CategoryTheory.ShortComplex.ShortExact

variable {R : Type u} [CommRing R] [IsLocalRing R]
variable {S : ShortComplex (ModuleCat.{v} R)}
variable [Module.Finite R S.X₁] [Module.Finite R S.X₃]

/-- The middle depth is at least the minimum
of the two endpoint depths. -/
@[stacks 00LX "middle term"]
theorem moduleDepth_middle_ge_min (hS : S.ShortExact) :
    moduleDepth R S.X₂ ≥ min (moduleDepth R S.X₁) (moduleDepth R S.X₃) := sorry

/-- The quotient depth is at least the
minimum of the middle depth and the predecessor of the submodule depth. -/
@[stacks 00LX "quotient term"]
theorem moduleDepth_right_ge_min (hS : S.ShortExact) :
    moduleDepth R S.X₃ ≥ min (moduleDepth R S.X₂) (moduleDepth R S.X₁ - 1) := sorry

/-- The submodule depth is at least the
minimum of the middle depth and the successor of the quotient depth. -/
@[stacks 00LX "submodule term"]
theorem moduleDepth_left_ge_min (hS : S.ShortExact) :
    moduleDepth R S.X₁ ≥ min (moduleDepth R S.X₂) (moduleDepth R S.X₃ + 1) := sorry

end CategoryTheory.ShortComplex.ShortExact

namespace Submodule

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- The canonical short complex associated to a submodule quotient. -/
@[stacks 00LX "canonical submodule quotient row"]
abbrev quotientShortComplex {M : Type v} [AddCommGroup M] [Module R M]
    (N : Submodule R M) : ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk N.subtype N.mkQ
    (LinearMap.exact_subtype_mkQ N).linearMap_comp_eq_zero

/-- The canonical sequence `0 → N → M → M ⧸ N → 0` is short exact. -/
@[stacks 00LX "short exact submodule quotient sequence"]
theorem quotientShortExact {M : Type v} [AddCommGroup M] [Module R M]
    (N : Submodule R M) :
    (quotientShortComplex (R := R) N).ShortExact := sorry

/-- The depth inequality for a submodule quotient when both endpoint modules are finite. -/
@[stacks 00LX "depth inequality for a finite submodule quotient"]
theorem moduleDepth_quotient_ge_min_of_finite
    {M : Type v} [AddCommGroup M] [Module R M] (N : Submodule R M)
    [Module.Finite R N] [Module.Finite R (M ⧸ N)] :
    moduleDepth R (M ⧸ N) ≥ min (moduleDepth R M) (moduleDepth R N - 1) := sorry

/-- In a Noetherian local ring, a finite ambient module gives the depth bound for every
submodule quotient. -/
@[stacks 00LX "depth inequality for a finite ambient submodule quotient"]
theorem moduleDepth_quotient_ge_min
    {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M] [IsNoetherianRing R]
    (N : Submodule R M) :
    moduleDepth R (M ⧸ N) ≥ min (moduleDepth R M) (moduleDepth R N - 1) := sorry

end Submodule
