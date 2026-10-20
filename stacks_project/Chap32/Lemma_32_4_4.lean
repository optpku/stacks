/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Limit.PointClosure
import StacksCheckRecall

open CategoryTheory Limits AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

section

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable (D : OrderDual I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
variable [∀ {i j : OrderDual I} (f : i ⟶ j), IsAffineHom (D.map f)]
variable (s : c.pt)

/- Lemma 32.4.4 (1): the residue field of a point of the limit is the colimit of the
residue fields of its stagewise images. -/
@[stacks 0CUG] #check
  (AlgebraicGeometry.Scheme.Limit.DirectedAffine.nonempty_isColimit_pointResidueFieldCocone
      D c hc s :
    Nonempty (IsColimit
      (AlgebraicGeometry.Scheme.Limit.DirectedAffine.pointResidueFieldCocone D c s)))

/- Lemma 32.4.4 (2): the closure of a point of the limit is the limit of the closures of
its stagewise images as underlying sets. -/
@[stacks 0CUG] #check
  (AlgebraicGeometry.Scheme.Limit.DirectedAffine.nonempty_isLimit_pointClosureSetCone
      D c hc s :
    Nonempty (IsLimit
      (AlgebraicGeometry.Scheme.Limit.DirectedAffine.pointClosureSetCone D c s)))

/- Lemma 32.4.4 (3): the reduced induced scheme on the closure of a point of the limit is
the limit of the reduced induced schemes on the stagewise point closures. -/
@[stacks 0CUG] #check
  (AlgebraicGeometry.Scheme.Limit.DirectedAffine.nonempty_isLimit_pointClosureSchemeCone
      D c hc s :
    Nonempty (IsLimit
      (AlgebraicGeometry.Scheme.Limit.DirectedAffine.pointClosureSchemeCone D c s)))

end

end AlgebraicGeometry
