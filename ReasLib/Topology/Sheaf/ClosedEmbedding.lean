/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Sheaf.Pushforward
public import ReasLib.Topology.Sheaf.Subset.Closed
import Mathlib.Tactic.CrossRefAttribute

/-!
# Direct image along a closed embedding

This leaf extends the exactness API for the inclusion of a closed subset to an arbitrary closed
embedding of topological spaces.
-/

@[expose] public section

open CategoryTheory

universe u

namespace TopCat.Sheaf.ClosedEmbedding.AddCommGrp

/-- The direct-image functor on abelian sheaves preserves exact sequences along a closed
embedding. -/
@[stacks 02UV "closed-embedding direct image is exact"]
theorem pushforwardExact {X Y : TopCat.{u}} {f : X ⟶ Y}
    (hf : Topology.IsClosedEmbedding f) :
    exactFunctor (X.Sheaf AddCommGrpCat.{u}) (Y.Sheaf AddCommGrpCat.{u})
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f) := sorry

end TopCat.Sheaf.ClosedEmbedding.AddCommGrp
