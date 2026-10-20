/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.GroupoidScheme

/- Lemma 39.18.3: Forgetting a restricted groupoid scheme to its underlying
pre-relation agrees with pulling back the underlying pre-relation. -/
@[stacks 02VD] #check
  (AlgebraicGeometry.GroupoidScheme.pullback_toPreRelation :
    {S : Scheme.{u}} → (G : GroupoidScheme S) → {U' : Over S} → (g : U' ⟶ G.U) →
      (G.pullback g).toPreRelation = G.toPreRelation.pullback g)

end AlgebraicGeometry.GroupoidScheme
