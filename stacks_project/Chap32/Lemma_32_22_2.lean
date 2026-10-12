/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Limit.FiniteTypeApproximation.Existence
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry

universe u

/- Lemma 32.22.2: in Situation 32.22.1, if `X ⟶ S` is quasi-separated and of finite
type, then after some stage `i` there is a diagram `X ⟶ W` over `S ⟶ S_i` with
`W ⟶ S_i` of finite type, and the induced morphism
`X ⟶ S ×_{S_i} W` is a closed immersion. -/
@[stacks 0CNN] #check
  (AlgebraicGeometry.FiniteTypeApproximationDiagram.exists_closedImmersion_of_finiteType :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
      [∀ j : I, IsNoetherian (D.obj j)]
      [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]
      {X : Scheme.{u}} (f : X ⟶ c.pt) [QuasiSeparated f] [Scheme.Hom.FiniteType f],
      ∃ (i : I) (diagram : FiniteTypeApproximationDiagram f (c.π.app i)),
        Scheme.Hom.FiniteType diagram.toSi ∧
          IsClosedImmersion (pullback.lift f diagram.toW diagram.w.symm))
