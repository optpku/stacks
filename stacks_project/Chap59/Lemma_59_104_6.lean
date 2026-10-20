/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Scheme.EtaleSheaf

/- Lemma 59.104.6: if `{f i : X_i i ⟶ X}` is an fppf covering family of
schemes, then the functor from Type-valued sheaves on `X.smallEtaleTopology`
to descent data for étale sheaves along that family is an equivalence of
categories. -/
@[stacks 0GF3] #check
  (AlgebraicGeometry.Scheme.EtaleSheaf.descentIsEquivalenceOfFppfCovering :
    ∀ {ι : Type v} {X : Scheme.{u}} {X_i : ι → Scheme.{u}}
      (f : ∀ i, X_i i ⟶ X) (h : FppfCovering (fun i ↦ Over.mk (f i))),
      (pseudofunctor.toDescentData f).IsEquivalence)

end AlgebraicGeometry.Scheme.EtaleSheaf
