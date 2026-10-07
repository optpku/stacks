module

import stacks_project.Chap76.Situation_76_52_7_BaseChange
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
variable [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsQuasiSeparated (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
variable (s : AlgebraicSpace.Limit.QcqsAffineLimit D) (X₀ : AlgebraicSpace S)
variable (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
variable [Flat x₀] [FinitePresentation x₀]

/- Situation 76.52.7: base change of a specified directed limit of qcqs algebraic spaces
with affine transition morphisms along a flat morphism of finite presentation. The
category `Over s.base` indexes the cofinal tail, and the pullbacks use the
canonically symmetric factor ordering. -/
@[stacks 0DKU] #check
  (AlgebraicGeometry.AlgebraicSpace.Limit.QcqsAffineLimit.flatFinitePresentationBaseChangeCone
    D s X₀ x₀ :
    Cone (AlgebraicGeometry.AlgebraicSpace.baseChangeOverDiagram D
      (OrderDual.toDual s.base) x₀))

end
