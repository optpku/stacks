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

/- Situation 75.24.1: a specified limit cone for a directed inverse system of
quasi-compact, absolutely quasi-separated algebraic spaces over `S` with affine
transition morphisms. Here `c.pt` is `X = lim X_i`, `c.π.app i` is the projection
`f_i`, `D.map (homOfLE h)` is the affine transition `f_{i'i}`, and `i0` is the
chosen `0 ∈ I`. -/
@[stacks 09RH] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.AbsolutelyQcqsAffineLimit.ofCone D c hc i0 :
    AlgebraicGeometry.AlgebraicSpace.Limit.AbsolutelyQcqsAffineLimit D)

end
