/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.PreRelation
import StacksCheckRecall

universe u

/- Lemma 39.13.2: the map to `G.U ⨯ G.U` underlying a groupoid scheme induces a
pre-equivalence relation on points over the base scheme. -/
@[stacks 0232] #check
  (AlgebraicGeometry.GroupoidScheme.toPreRelation_isPreEquivalence :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} (G : AlgebraicGeometry.GroupoidScheme S),
      G.toPreRelation.IsPreEquivalence)
