module

import ReasLib.AlgebraicGeometry.Scheme.Limit.QcqsAffine
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry

universe u

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) (i0 : I)
variable [∀ j, CompactSpace (D.obj j)] [∀ j, QuasiSeparatedSpace (D.obj j)]
variable [∀ {j j' : I} (hjj' : j ≤ j'), IsAffineHom (D.map (homOfLE hjj'))]

/- Situation 32.4.5: a specified limit cone for a directed inverse system of quasi-compact,
quasi-separated schemes with affine transition morphisms, together with a distinguished index. -/
@[stacks 086P] #check
  (AlgebraicGeometry.Scheme.Limit.QcqsAffineLimit.ofCone D c hc i0 :
    AlgebraicGeometry.Scheme.Limit.QcqsAffineLimit D)

end
