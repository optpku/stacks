/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

/-!
# Cardinal bounds for ordinal cofinalities
-/

@[expose] public section

universe u

namespace Cardinal

/-- Every cardinal is strictly below the cofinality of some ordinal in the same universe. -/
theorem exists_ord_cof_gt (κ : Cardinal.{u}) : ∃ o : Ordinal.{u}, κ < o.cof := sorry

end Cardinal
