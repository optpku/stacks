/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Action.Module.Quasicoherent
import StacksCheckRecall

universe u

open AlgebraicGeometry CategoryTheory

variable {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
  (X : GroupAlgebraicSpace.Action G)

/- Lemma 78.15.2: Let `B → S` as in Section 78.3. Let `G` be a group algebraic space
over `B`. Let `X` be an algebraic space over `B` with an action `a : G ×_B X ⟶ X`
of `G` on `X` over `B`. Let `(U, R, s, t, c)` be the groupoid in algebraic spaces
from Lemma 78.15.1. The identity-on-data rule `(F, α) ↦ (F, α)` is an equivalence
of categories between `G`-equivariant `𝒪_X`-modules and quasi-coherent modules on
`(U, R, s, t, c)`. -/
@[stacks 0445] #check
  (AlgebraicGeometry.AlgebraicSpace.QCoh.Equivariant.equivalenceActionGroupoid G X :
    CategoryTheory.Equivalence (AlgebraicGeometry.AlgebraicSpace.QCoh.Equivariant G X)
      (AlgebraicGeometry.GroupoidAlgebraicSpace.QCoh
        (AlgebraicGeometry.GroupoidAlgebraicSpace.ofAction G X)))

/- Companion: the action groupoid has target `t = a` and source `s = pr`. -/
#check GroupoidAlgebraicSpace.ofAction_t
#check GroupoidAlgebraicSpace.ofAction_s

/- Companion: objects of `Equivariant G X` are pairs `(F, α)` recovered by `of`,
`obj`, and `alpha`. -/
#check AlgebraicSpace.QCoh.Equivariant.of
#check AlgebraicSpace.QCoh.Equivariant.obj
#check AlgebraicSpace.QCoh.Equivariant.alpha
