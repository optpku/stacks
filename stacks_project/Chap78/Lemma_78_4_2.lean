/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Pullback
import stacks_project.Chap65.Lemma_65_7_3_Pullback
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 78.4.2 (1): the pullback of a pre-relation along `g : U' ⟶ U` is a
pre-relation on `U'` over `B`. -/
@[stacks 043D] #check (@AlgebraicGeometry.AlgebraicSpace.PreRelation.pullback :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
    [CategoryTheory.Limits.HasPullbacks (AlgebraicGeometry.AlgebraicSpace S)]
    {U U' : Over B},
    AlgebraicGeometry.AlgebraicSpace.PreRelation U → (U' ⟶ U) →
      AlgebraicGeometry.AlgebraicSpace.PreRelation U')

/- Lemma 78.4.2 (2): pullback preserves the relation condition. -/
@[stacks 043D] #check (@AlgebraicGeometry.AlgebraicSpace.PreRelation.instMonoHomPullback :
  ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
    [CategoryTheory.Limits.HasPullbacks (AlgebraicGeometry.AlgebraicSpace S)]
    {U U' : Over B} (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U)
    (g : U' ⟶ U) [Mono P.hom],
      Mono (P.pullback g).hom)

/- Lemma 78.4.2 (3): pullback preserves pre-equivalence relations. -/
@[stacks 043D] #check
  (@AlgebraicGeometry.AlgebraicSpace.PreRelation.IsPreEquivalence.pullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      [CategoryTheory.Limits.HasPullbacks (AlgebraicGeometry.AlgebraicSpace S)]
      {U U' : Over B} {P : AlgebraicGeometry.AlgebraicSpace.PreRelation U},
        P.IsPreEquivalence → (g : U' ⟶ U) → (P.pullback g).IsPreEquivalence)

/- Lemma 78.4.2 (4): pullback preserves internal equivalence relations. -/
@[stacks 043D] #check
  (@AlgebraicGeometry.AlgebraicSpace.PreRelation.instIsEquivalenceRelationPullback :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      [CategoryTheory.Limits.HasPullbacks (AlgebraicGeometry.AlgebraicSpace S)]
      {U U' : Over B} (P : AlgebraicGeometry.AlgebraicSpace.PreRelation U)
      (g : U' ⟶ U) [IsEquivalenceRelation P.t P.s],
        IsEquivalenceRelation (P.pullback g).t (P.pullback g).s)
