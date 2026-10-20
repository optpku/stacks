/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Limit.FinitePresentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open scoped Bicategory

universe u

/- Lemma 102.5.1: if `X = lim X_i` is a directed inverse limit of quasi-compact
quasi-separated algebraic spaces with affine transitions, then every algebraic
stack of finite presentation over `X` descends to some stage: there exist `i`
and an algebraic stack `𝒳_i` of finite presentation over `X_i` with
`𝒳 ≅ 𝒳_i ×_{X_i} X` as algebraic stacks over `X`. -/
@[stacks 0CN4] #check
  (AlgebraicGeometry.AlgebraicStack.Limit.FinitePresentation.exists_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
      (c : Cone D) (hc : IsLimit c)
      [∀ j, AlgebraicSpace.IsQuasiCompact (D.obj j)]
      [∀ j, AlgebraicSpace.IsAbsolutelyQuasiSeparated (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), AlgebraicSpace.Affine (D.map (homOfLE hjj'))]
      {X : GroupoidsOver S} [AlgebraicStack X]
      (f : X ⟶ c.pt.toGroupoids) [AlgebraicStack.FinitePresentation f],
      ∃ (i : I) (Xi : GroupoidsOver S) (hXi : AlgebraicStack Xi)
        (fi : Xi ⟶ (D.obj i).toGroupoids)
        (hfi : AlgebraicStack.FinitePresentation fi)
        (e : X ≌ AlgebraicStack.pullback fi (c.π.app i)),
        Nonempty (e.hom ≫ AlgebraicStack.pullbackSnd fi (c.π.app i) ≅ f))
