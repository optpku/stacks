/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap67.Lemma_67_48_6_Reduced
public import stacks_project.Chap70.Lemma_70_4_1_Limit

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

/-- Lemma 70.4.4: Let `S` be a scheme. Let `I` be a directed set. Let
`(X_i, f_{i'i})` be an inverse system over `I` of algebraic spaces over `S`
with affine transition morphisms, and write `X = lim_i X_i` for the inverse
limit. If `X_i` is reduced for all `i`, then `X` is reduced. -/
@[stacks 0CUI]
instance isReduced_limit [∀ i : OrderDual I, IsReduced (D.obj i)] :
    IsReduced (Limits.limit D) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DirectedAffine
