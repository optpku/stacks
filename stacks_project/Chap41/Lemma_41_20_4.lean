/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.DescentData.Etale.Effectivity.Local

open CategoryTheory CategoryTheory.Limits

universe u v

/-
Lemma 41.20.4: An étale descent datum is effective if it is effective over an open
cover, the restricted canonical functors are fully faithful on pairwise intersections,
and they are faithful on triple intersections.
-/
@[stacks 0BTM] #check
  (AlgebraicGeometry.Scheme.DescentData.Etale.IsEffective.ofOpenCover :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      (D : AlgebraicGeometry.Scheme.DescentData.Etale f)
      {ι : Type v} (U : ι → S.Opens) (hU : TopologicalSpace.IsOpenCover U),
      (∀ i, ((AlgebraicGeometry.Scheme.DescentData.Etale.baseChangeFunctor
          f (U i).ι).obj D).IsEffective) →
        (∀ i j, Nonempty
          (AlgebraicGeometry.Scheme.DescentData.Etale.canonicalFunctor
            (pullback.snd f (U i ⊓ U j).ι)).FullyFaithful) →
        (∀ i j k,
          (AlgebraicGeometry.Scheme.DescentData.Etale.canonicalFunctor
            (pullback.snd f (U i ⊓ U j ⊓ U k).ι)).Faithful) →
        D.IsEffective)
