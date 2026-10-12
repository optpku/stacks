/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicTopology.SimplicialObject.Evaluation
public import ReasLib.AlgebraicTopology.SimplicialSet.StdSimplex.Contractible
import Mathlib.Tactic.CrossRefAttribute

/-!
# Pointlike Hom spaces of the simplex category

The identity cosimplicial object on `SimplexCategory` has standard simplices as its Hom spaces,
so each is simplicially homotopy equivalent to a point.
-/

@[expose] public section

open CategoryTheory

namespace SimplexCategory

/-- The identity cosimplicial object on the simplex category has pointlike Hom spaces. -/
@[stacks 08QD "identity simplex-category Hom spaces"]
theorem identity_hasHomSpaces :
    CosimplicialObject.Pointlike.HasHomSpaces (𝟭 SimplexCategory) := sorry

end SimplexCategory
