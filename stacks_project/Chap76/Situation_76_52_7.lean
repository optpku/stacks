/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.BaseChange
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Limit.AbsolutelyQcqs
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Flat
import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FinitePresentation

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
variable [∀ i, IsQuasiCompact (D.obj i)] [∀ i, IsAbsolutelyQuasiSeparated (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
variable (s : AlgebraicSpace.Limit.AbsolutelyQcqsAffineLimit D) (X₀ : AlgebraicSpace S)
variable (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
variable [Flat x₀] [FinitePresentation x₀]

/- Situation 76.52.7: base change of a specified directed limit of quasi-compact,
absolutely quasi-separated algebraic spaces with affine transition morphisms along
a flat morphism of finite presentation. The category `Over (OrderDual.toDual s.base)`
indexes the cofinal tail i ≥ 0. Its diagram maps are the canonical transitions, and
the induced cone legs are the projections from the limiting fibre product.
The pullbacks put Yᵢ (respectively Y) first and X₀ second, as in the source;
the base-change construction uses the canonical symmetry of fibre products. -/
@[stacks 0DKU] #check
  (AlgebraicGeometry.AlgebraicSpace.baseChangeOverCone
    D s.limitCone.cone (OrderDual.toDual s.base) x₀ :
    Cone (AlgebraicGeometry.AlgebraicSpace.baseChangeOverDiagram D
      (OrderDual.toDual s.base) x₀))

variable {j : OrderDual I} (g : j ⟶ OrderDual.toDual s.base)

#check
  (AlgebraicGeometry.AlgebraicSpace.baseChangeOverDiagram_obj D
    (OrderDual.toDual s.base) x₀ g :
    (AlgebraicGeometry.AlgebraicSpace.baseChangeOverDiagram D
      (OrderDual.toDual s.base) x₀).obj (Over.mk g) = pullback (D.map g) x₀)

#check
  (AlgebraicGeometry.AlgebraicSpace.baseChangeOverCone_pt D s.limitCone.cone
    (OrderDual.toDual s.base) x₀ :
    (AlgebraicGeometry.AlgebraicSpace.baseChangeOverCone D s.limitCone.cone
      (OrderDual.toDual s.base) x₀).pt =
      pullback (s.limitCone.cone.π.app (OrderDual.toDual s.base)) x₀)

end
