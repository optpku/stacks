module

public import stacks_project.Chap102.Lemma_102_5_1_FinitePresentation
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.AlgebraicStack.Limit.FinitePresentation
open scoped Bicategory

universe u

/- Lemma 102.5.1: if `X = lim X_i` is a directed inverse limit of quasi-compact
quasi-separated algebraic spaces with affine transitions, then every algebraic
stack of finite presentation over `X` descends to some stage: there exist `i`
and an algebraic stack `𝒳_i` of finite presentation over `X_i` with
`𝒳 ≅ 𝒳_i ×_{X_i} X` as algebraic stacks over `X`. -/
@[stacks 0CN4] #check
  (exists_stage :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
      (c : Cone D) (hc : IsLimit c)
      [∀ j, AlgebraicSpace.IsQuasiCompact (D.obj j)]
      [∀ j, AlgebraicSpace.IsQuasiSeparated (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), AlgebraicSpace.Affine (D.map (homOfLE hjj'))]
      {X : GroupoidsOver S} [AlgebraicStack X]
      (f : X ⟶ c.pt.toGroupoids) [AlgebraicStack.FinitePresentation f],
      ∃ (i : I) (Xi : GroupoidsOver S) (hXi : AlgebraicStack Xi)
        (fi : Xi ⟶ (D.obj i).toGroupoids)
        (hfi : AlgebraicStack.FinitePresentation fi)
        (e : X ≌ limitPullback c fi),
        Nonempty (e.hom ≫ limitPullback.snd c fi ≅ f))
