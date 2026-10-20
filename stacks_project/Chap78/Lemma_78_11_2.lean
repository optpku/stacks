/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import stacks_project.Chap78.Lemma_78_11_2_Groupoid
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.PreRelation
import StacksCheckRecall

universe u

/- Lemma 78.11.2: given a groupoid in algebraic spaces over `B`, the morphism
`j = (t, s) : R ⟶ U ⨯ U` is a pre-equivalence relation. -/
@[stacks 043X] #check
  (AlgebraicGeometry.GroupoidAlgebraicSpace.toPreRelation_isPreEquivalence :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {B : AlgebraicGeometry.AlgebraicSpace S}
      (G : AlgebraicGeometry.GroupoidAlgebraicSpace B),
      G.toPreRelation.IsPreEquivalence)
