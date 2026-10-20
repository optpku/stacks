/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Limit.QcqsAffine
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry

universe u

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c) (i0 : I)
variable [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
variable [∀ {i i' : I} (h : i ≤ i'), IsAffineHom (D.map (homOfLE h))]

/- Situation 36.29.1: for a directed inverse system of quasi-compact, quasi-separated schemes
with affine transition morphisms, `c.pt` is the specified limit scheme, `c.π.app i` are its
projections, and `i0` is the distinguished index. -/
@[stacks 09RD] #check
  (AlgebraicGeometry.Scheme.Limit.QcqsAffineLimit.ofCone D c hc i0 :
    AlgebraicGeometry.Scheme.Limit.QcqsAffineLimit D)

end
