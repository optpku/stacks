/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.ChowMotive
public import ReasLib.AlgebraicGeometry.Correspondence.GradedCategory.Linear
public import Mathlib.CategoryTheory.Preadditive.Biproducts

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ChowMotive

variable (k : Type u) [Field k]

/-- The category of Chow motives over a field admits finite biproducts. -/
instance instHasFiniteBiproducts :
    HasFiniteBiproducts
      (ChowMotive k (fun _ ↦ AlgebraicGeometry.Correspondence.GradedCategory k)) :=
  sorry

end ChowMotive
