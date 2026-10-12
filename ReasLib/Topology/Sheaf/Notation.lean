/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Set-valued presheaf and sheaf notation

The textbook notations for set-valued presheaves and sheaves on a topological space belong to the
topological sheaf API, rather than to any chapter that happens to introduce them.
-/

@[expose] public section

namespace TopCat

/-- `PSh(X)` is the category of set-valued presheaves on the topological space `X`. -/
scoped notation "PSh(" X ")" => TopCat.Presheaf (Type _) X

/-- `Sh(X)` is the category of set-valued sheaves on the topological space `X`. -/
scoped notation "Sh(" X ")" => TopCat.Sheaf (Type _) X

end TopCat
