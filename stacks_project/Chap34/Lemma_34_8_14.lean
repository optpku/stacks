/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Sites.Ph.AffineComparison
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 34.8.14 (1): the inclusion from affine schemes over `S` to schemes over `S` is
cocontinuous for the affine and big ph topologies. -/
@[stacks 0DBP] #check
  (AlgebraicGeometry.Scheme.Ph.AffineComparison.isCocontinuous :
    ∀ (S : AlgebraicGeometry.Scheme.{u}),
      (AlgebraicGeometry.Scheme.AffineOver.forget S).IsCocontinuous
        (AlgebraicGeometry.Scheme.bigAffinePhTopology S)
        (AlgebraicGeometry.Scheme.bigPhSite S))

/- Lemma 34.8.14 (2): the cocontinuous direct image from affine ph sheaves to big ph sheaves
is an equivalence. -/
@[stacks 0DBP] #check
  (AlgebraicGeometry.Scheme.Ph.AffineComparison.directImageIsEquivalence :
    ∀ (S : AlgebraicGeometry.Scheme.{u}),
      ((AlgebraicGeometry.Scheme.AffineOver.forget S).sheafPushforwardCocontinuous
        (Type (u + 1)) (AlgebraicGeometry.Scheme.bigAffinePhTopology S)
        (AlgebraicGeometry.Scheme.bigPhSite S)).IsEquivalence)
