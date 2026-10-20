/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
public import ReasLib.Algebra.Homology.ChainComplex.DualNumber.Periodic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Projective dimension of the dual-number residue module

The periodic resolution of the residue module over the dual numbers consists of projective terms,
but the residue module has infinite projective dimension.

@stack 0A5Q
-/

@[expose] public section

open CategoryTheory

universe u

namespace DualNumber.Periodic

variable (k : Type u) [Field k]

/-- Every term of the periodic dual-number resolution is projective. -/
@[stacks 0A5Q "projective terms in the periodic resolution"]
instance termProjective (n : ℕ) : Projective ((complex k).X n) := sorry

/-- The residue module over the dual numbers of a field is not projective. -/
@[stacks 0A5Q "the dual-number residue module is not projective"]
theorem residueModule_not_projective : ¬ Projective (residueModule k) := sorry

/-- Example 15.69.3: the residue module over the dual numbers of a field has infinite projective
dimension. -/
@[stacks 0A5Q "Example 15.69.3"]
theorem residueModule_projectiveDimension_eq_top :
    projectiveDimension (residueModule k) = ⊤ := sorry

end DualNumber.Periodic
