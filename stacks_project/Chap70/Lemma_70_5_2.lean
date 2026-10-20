/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DirectedAffine.Topology
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 70.5.2: With same notation and assumptions as in Lemma 70.5.1 we have
`|X| = lim_i |X_i|` as topological spaces, as `IsLimit (forgetToTop.mapCone c)`. -/
@[stacks 086V] #check
  (AlgebraicGeometry.AlgebraicSpace.DirectedAffine.isLimit_forgetToTop_mapCone :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
      [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
      [∀ i : OrderDual I, IsDecent (D.obj i)]
      (c : Cone D),
      IsLimit c → IsLimit (forgetToTop.mapCone c))
