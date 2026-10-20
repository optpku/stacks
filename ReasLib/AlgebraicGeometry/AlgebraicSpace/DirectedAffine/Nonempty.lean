/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.DirectedAffine.Limit
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact

/-!
# Nonemptiness of directed affine inverse limits of algebraic spaces

A directed inverse limit of nonempty quasi-compact algebraic spaces with affine
transitions is nonempty.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits (Cone IsLimit)

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DirectedAffine

variable {I : Type u} [Preorder I] [h_nonempty : Nonempty I]
variable [h_directed : IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
variable [h_affine : ∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]
include h_nonempty h_directed h_affine

/-- The vertex of a limiting cone over a directed inverse system of quasi-compact
nonempty algebraic spaces with affine transition morphisms has nonempty points. -/
theorem nonempty_of_isLimit
    [h_stage_nonempty : ∀ i : OrderDual I, Nonempty (Points (D.obj i))]
    [h_quasiCompact : ∀ i : OrderDual I, IsQuasiCompact (D.obj i)]
    (c : Cone D) (hc : IsLimit c) :
    Nonempty (Points c.pt) := sorry

/-- The chosen directed affine inverse limit of quasi-compact nonempty algebraic spaces
has nonempty points. -/
instance instNonempty_points_limit
    [h_stage_nonempty : ∀ i : OrderDual I, Nonempty (Points (D.obj i))]
    [h_quasiCompact : ∀ i : OrderDual I, IsQuasiCompact (D.obj i)] :
    Nonempty (Points (Limits.limit D)) := sorry

end AlgebraicGeometry.AlgebraicSpace.DirectedAffine
