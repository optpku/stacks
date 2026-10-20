/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.ChosenPresentation.Independence
import StacksCheckRecall

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.ChosenBigEtaleSite

/- Lemma 59.21.2: if a scheme `S` is represented in two chosen big étale-site
presentations, then the resulting small étale topoi are equivalent. -/
@[stacks 0958] #check (AlgebraicGeometry.ChosenBigEtaleSite.smallToposIndependent :
  ∀ (S : Scheme.{u})
    (X : ChosenBigEtaleSite.{u, v}) (Y : ChosenBigEtaleSite.{u, w})
    (SX : X.carrier) (SY : Y.carrier)
    (hX : X.toScheme.obj SX = S) (hY : Y.toScheme.obj SY = S),
    (smallToposComparison S X Y SX SY hX hY).IsEquivalence)

end AlgebraicGeometry.ChosenBigEtaleSite
