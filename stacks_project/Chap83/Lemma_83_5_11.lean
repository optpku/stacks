/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.ReducedInvariant
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 83.5.11
In the situation of Definition 83.5.8, a morphism that is set-theoretically invariant is invariant
when the pre-relation is reduced and the target is locally separated over the base. -/
@[stacks 048Y] #check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.isInvariant_of_isSetTheoreticallyInvariant :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
      [AlgebraicSpace.LocallySeparated X.hom] (P : PreRelation U)
      [AlgebraicSpace.IsReduced P.left.left] {φ : U ⟶ X},
      P.IsSetTheoreticallyInvariant φ → P.IsInvariantHom φ)

#check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.isInvariant_iff_isSetTheoreticallyInvariant :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
      [AlgebraicSpace.LocallySeparated X.hom] (P : PreRelation U)
      [AlgebraicSpace.IsReduced P.left.left] (φ : U ⟶ X),
      P.IsInvariantHom φ ↔ P.IsSetTheoreticallyInvariant φ)
