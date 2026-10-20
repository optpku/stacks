/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DirectedAffine.Limit

/-!
# Reducedness of directed affine inverse limits

The inverse limit of a directed system of reduced algebraic spaces with affine
transition morphisms is reduced.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DirectedAffine

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} {D : OrderDual I ⥤ AlgebraicSpace S}
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]

/-- The inverse limit of a nonempty directed system of reduced algebraic spaces
over a scheme with affine transition morphisms is reduced. -/
@[stacks 0CUI]
instance isReduced_limit [∀ i : OrderDual I, IsReduced (D.obj i)] :
    IsReduced (Limits.limit D) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DirectedAffine
