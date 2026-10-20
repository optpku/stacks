/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidScheme.Restriction.Comparison

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.GroupoidScheme

/- The canonical morphism comparing two successive restrictions of a groupoid scheme. -/
#check
  (AlgebraicGeometry.GroupoidScheme.restrictionComparison :
    ∀ {S : Scheme.{u}} (G : GroupoidScheme S) {U' U'' : Over S}
      (g : U' ⟶ G.U) (g' : U'' ⟶ U'),
      Limits.pullback (pullback.snd g G.t ≫ G.s)
          (pullback.snd (g' ≫ g) G.t ≫ G.s) ⟶
        Limits.pullback g' (G.toPreRelation.pullback g).t)

end AlgebraicGeometry.GroupoidScheme
