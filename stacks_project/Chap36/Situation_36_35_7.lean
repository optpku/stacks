/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Limit.QcqsAffine.BaseChange
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry

universe u

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u})
variable [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]
variable (s : Scheme.Limit.QcqsAffineLimit D) (X₀ : Scheme.{u})
variable (x₀ : X₀ ⟶ D.obj (OrderDual.toDual s.base))
variable [Flat x₀] [Scheme.Hom.FinitePresentation x₀]

/- Situation 36.35.7: base change of a specified directed limit of qcqs schemes with affine
transition morphisms along a flat morphism of finite presentation. The category `Over s.base`
indexes the cofinal tail, and the pullbacks use the canonically symmetric factor ordering. -/
@[stacks 0DI6] #check
  (AlgebraicGeometry.Scheme.Limit.QcqsAffineLimit.flatFinitePresentationBaseChangeCone
    D s X₀ x₀ :
    Cone (AlgebraicGeometry.Scheme.baseChangeOverDiagram D
      (OrderDual.toDual s.base) x₀))

end
