/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.Topology

@[expose] public section

open CategoryTheory
open MonoidalCategory MonObj CartesianMonoidalCategory

universe u

/- Lemma 39.7.2: For an open subscheme `U` of a group scheme `G` over a field `k`,
the image of `T ×_k U` in `G` under multiplication by a morphism `f : T ⟶ G` is open. -/
@[stacks 0B7N] #check
  (AlgebraicGeometry.GroupScheme.isOpen_range_mul_open :
    ∀ {k : Type u} [Field k] (G : AlgebraicGeometry.SchemeOverField k) [GrpObj G]
      {T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ G.left) (U : G.left.Opens),
      let TOver : AlgebraicGeometry.SchemeOverField k := Over.mk (f ≫ G.hom)
      let fOver : TOver ⟶ G := Over.homMk f
      let UOver : AlgebraicGeometry.SchemeOverField k := Over.mk (U.ι ≫ G.hom)
      let uOver : UOver ⟶ G := Over.homMk U.ι
      IsOpen (Set.range (((fOver ⊗ₘ uOver) ≫ μ[G]).left.base)))
