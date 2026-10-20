/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DirectedAffine.Pullback
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 70.4.2: Let `S` be a scheme. Let `I` be a directed set. Let
`(X_i, f_{ii'})` be an inverse system over `I` of algebraic spaces over `S`
with affine transition maps. Let `X = lim_i X_i`. Let `0 ∈ I`. Suppose that
`T ⟶ X_0` is a morphism of algebraic spaces. Then
`T ×_{X_0} X = lim_{i ≥ 0} T ×_{X_0} X_i` as algebraic spaces over `S`. -/
@[stacks 07SH] #check (AlgebraicGeometry.AlgebraicSpace.DirectedAffine.pullback_π_iso :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
      [h_affine : ∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))],
      ∀ (i : I) {T : AlgebraicSpace S} (g : T ⟶ D.obj (OrderDual.toDual i)),
        Limits.pullback (Limits.limit.π D (OrderDual.toDual i)) g ≅
          AlgebraicGeometry.AlgebraicSpace.DirectedAffine.limit
            (AlgebraicGeometry.AlgebraicSpace.DirectedAffine.pullbackTail D i g))
