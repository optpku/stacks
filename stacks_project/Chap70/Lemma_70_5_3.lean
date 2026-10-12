/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap70.Lemma_70_4_1_Limit
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Definition_66_5_1_QuasiCompact

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
variable [h_stage_nonempty : ∀ i : OrderDual I, Nonempty (Points (D.obj i))]
variable [h_quasiCompact : ∀ i : OrderDual I, IsQuasiCompact (D.obj i)]

include h_nonempty h_directed h_affine h_stage_nonempty h_quasiCompact

/-- Lemma 70.5.3: Let `S` be a scheme. Let `X = lim_i X_i` be the limit of a directed
inverse system of algebraic spaces over `S` with affine transition morphisms
(Lemma 70.4.1). If each `X_i` is quasi-compact and nonempty, then `|X|` is nonempty,
as `Nonempty (Points c.pt)`. -/
@[stacks 086W]
theorem nonempty_of_isLimit (c : Cone D) (hc : IsLimit c) :
    Nonempty (Points c.pt) := sorry

/-- The chosen directed affine inverse limit of quasi-compact nonempty algebraic spaces
has nonempty points. -/
instance instNonempty_points_limit : Nonempty (Points (Limits.limit D)) := sorry

end AlgebraicGeometry.AlgebraicSpace.DirectedAffine
