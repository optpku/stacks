module

public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import ReasLib.Algebra.Category.ModuleCat.DualNumber.Residue
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory
open scoped DualNumber

universe u

namespace DualNumber

variable (k : Type u) [Field k]

/-- The residue module over the dual numbers has nontrivial Ext with itself in every degree. -/
theorem residueExt_nontrivial (i : ℕ) :
    Nontrivial (Abelian.Ext (residueModule k) (residueModule k) i) := sorry

end DualNumber
