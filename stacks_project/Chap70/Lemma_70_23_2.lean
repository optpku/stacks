/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap70.Lemma_70_23_2_Existence
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 70.23.2: in Situation 70.23.1, if `X ⟶ B` is quasi-separated and of
finite type, then after some stage `i` there is a diagram `X ⟶ W` over
`B ⟶ B_i` with `W ⟶ B_i` of finite type, and the induced morphism
`X ⟶ B ×_{B_i} W` is a closed immersion. -/
@[stacks 0CP7] #check
  (AlgebraicGeometry.AlgebraicSpace.FiniteTypeApproximationDiagram.exists_closedImmersion_of_finiteType :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
      (c : Cone D) (hc : IsLimit c)
      [∀ j : I, IsNoetherian (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]
      {X : AlgebraicSpace S} (f : X ⟶ c.pt) [QuasiSeparated f] [FiniteType f],
      ∃ (i : I) (diagram : FiniteTypeApproximationDiagram f (c.π.app i)),
        FiniteType diagram.toBi ∧
          IsClosedImmersion (pullback.lift f diagram.toW diagram.comm.w.symm))
