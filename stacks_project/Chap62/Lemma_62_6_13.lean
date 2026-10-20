/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RelativeCycle.InverseLimit
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

/- Lemma 62.6.13. Relative cycle groups commute with directed inverse limits of
Noetherian schemes with affine transition morphisms and Noetherian limit. -/
@[stacks 0H5D] #check
  (AlgebraicGeometry.RelativeCycle.InverseLimit.toLimitGroup_bijective :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ j, IsNoetherian (D.obj j)] [IsNoetherian c.pt]
      [∀ {j j' : I} (h : j ≤ j'), IsAffineHom (D.map (homOfLE h))]
      (i0 : I) {X0 : Scheme.{u}} (f0 : X0 ⟶ D.obj i0) [f0.FiniteType] (r : ℕ),
      Function.Bijective
        (AlgebraicGeometry.RelativeCycle.InverseLimit.toLimitGroup D c i0 f0 r))
