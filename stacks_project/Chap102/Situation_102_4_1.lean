/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.AbsolutelyQcqs
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
variable (c : Cone D) (hc : IsLimit c) (i0 : I)
variable [∀ j, IsQuasiCompact (D.obj j)] [∀ j, IsAbsolutelyQuasiSeparated (D.obj j)]
variable [∀ {j j' : I} (hjj' : j ≤ j'), Affine (D.map (homOfLE hjj'))]

/- Situation 102.4.1: a specified limit cone for a directed inverse system of
quasi-compact, absolutely quasi-separated algebraic spaces over `S` with affine
transition morphisms. Absolute quasi-separatedness concerns the spaces themselves
and imposes no separation assumption on `S`. Here `D.obj i` is the stage `Y_i`
(the live Stacks text writes `X_i` for this qcqs hypothesis), `c.pt` is
`Y = lim_i Y_i`, `D.map (homOfLE h)` is
the affine transition `Y_{i'} ⟶ Y_i`, `c.π.app i` is the projection `Y ⟶ Y_i`,
and `i0` is the chosen `0 ∈ I`. -/
@[stacks 0CPY] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.AbsolutelyQcqsAffineLimit.ofCone D c hc i0 :
    AlgebraicGeometry.AlgebraicSpace.Limit.AbsolutelyQcqsAffineLimit D)

end
