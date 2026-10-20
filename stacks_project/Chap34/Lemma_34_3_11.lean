/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Zariski.SmallAffineComparison
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 34.3.11: the inclusion of affine opens of `S` into its small Zariski site is special
cocontinuous for the standard small affine and small Zariski topologies. -/
@[stacks 0F1B] #check
  (AlgebraicGeometry.Scheme.Zariski.SmallAffineComparison.isSpecialCocontinuous :
    ∀ (S : AlgebraicGeometry.Scheme.{u}),
      (AlgebraicGeometry.Scheme.smallAffineZariskiInclusion S).IsSpecialCocontinuous
        (AlgebraicGeometry.Scheme.smallAffineZariskiTopology S)
        (AlgebraicGeometry.Scheme.smallZariskiTopology S))

/- Its cocontinuous direct image from sheaves on affine opens to sheaves on the small Zariski
site is an equivalence. -/
#check
  (AlgebraicGeometry.Scheme.Zariski.SmallAffineComparison.directImageIsEquivalence :
    ∀ (S : AlgebraicGeometry.Scheme.{u}),
      ((AlgebraicGeometry.Scheme.smallAffineZariskiInclusion S).sheafPushforwardCocontinuous
        (Type u) (AlgebraicGeometry.Scheme.smallAffineZariskiTopology S)
        (AlgebraicGeometry.Scheme.smallZariskiTopology S)).IsEquivalence)
