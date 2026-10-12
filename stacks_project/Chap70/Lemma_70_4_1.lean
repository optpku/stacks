/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap70.Lemma_70_4_1_Limit
public import stacks_project.Chap70.Lemma_70_4_1_Pullback

/-!
# Lemma 70.4.1

A directed inverse system of algebraic spaces with affine transitions has an
inverse limit, affine projections, and fibre products commuting with the
directed limit over a cofinal tail.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace
open CategoryTheory.Limits (IsLimit)

universe u

namespace AlgebraicGeometry.AlgebraicSpace.DirectedAffine

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
variable {S : Scheme.{u}} (D : OrderDual I ⥤ AlgebraicSpace S)
variable [∀ {i i' : I} (h : i ≤ i'), Affine (D.map (homOfLE h))]

/-- Lemma 70.4.1 (1): Let `S` be a scheme. Let `I` be a directed set. Let
`(X_i, f_{ii'})` be an inverse system over `I` in the category of algebraic
spaces over `S`. If the morphisms `f_{ii'} : X_i ⟶ X_{i'}` are affine, then
the limit `X = lim_i X_i` (as an fppf sheaf) is an algebraic space. -/
@[stacks 07SF]
theorem functorOfPoints_limit :
    (limit D).functorOfPoints = Limits.limit (D ⋙ forgetToPresheaf) :=
  sorry

/-- Lemma 70.4.1 (2): each of the morphisms `f_i : X ⟶ X_i` is affine. -/
@[stacks 07SF]
instance affine_limit_π (i : OrderDual I) : Affine (Limits.limit.π D i) :=
  affine_π D i

/-- Lemma 70.4.1 (3): for any `i ∈ I` and any morphism of algebraic spaces
`T ⟶ X_i` we have `X ×_{X_i} T = lim_{i' ≥ i} X_{i'} ×_{X_i} T` as algebraic
spaces over `S`. -/
@[stacks 07SF]
noncomputable def fibreProduct_isLimit (i : I) {T : AlgebraicSpace S}
    (g : T ⟶ D.obj (OrderDual.toDual i)) :
    IsLimit (pullbackCone D i g) :=
  isLimit_pullbackCone D i g

end AlgebraicGeometry.AlgebraicSpace.DirectedAffine
