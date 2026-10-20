/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Points

/-!
# Points of a pre-relation of algebraic spaces

A pre-relation `j : R ⟶ U ×_B U` of algebraic spaces over `B` induces a relation on the
set of points `|U|`. If `j` is a pre-equivalence relation, that relation is an equivalence
relation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.PreRelation.pointsRel_equivalence :
    ∀ {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B} (P : PreRelation U),
      P.IsPreEquivalence → Equivalence (PreRelation.pointsRel P))
