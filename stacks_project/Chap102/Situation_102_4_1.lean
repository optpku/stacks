/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import stacks_project.Chap70.Situation_70_5_5_QcqsAffine
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
variable (c : Cone D) (hc : IsLimit c) (i0 : I)
variable [∀ j, IsQuasiCompact (D.obj j)] [∀ j, IsQuasiSeparated (D.obj j)]
variable [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]

/- Situation 102.4.1: a specified limit cone for a directed inverse system of
quasi-compact, quasi-separated algebraic spaces over `S` with affine transition
morphisms. Here `D.obj i` is the stage `Y_i` (the live Stacks text writes `X_i`
for this qcqs hypothesis), `c.pt` is `Y = lim_i Y_i`, `D.map (homOfLE h)` is
the affine transition `Y_{i'} ⟶ Y_i`, `c.π.app i` is the projection `Y ⟶ Y_i`,
and `i0` is the chosen `0 ∈ I`. -/
@[stacks 0CPY] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit.ofCone D c hc i0 :
    AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit D)

end
