/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_19_4_AutomorphismGroup

/-!
# Independence of automorphism-group isomorphisms on a representative

For a morphism `f : X ⟶ Y` of algebraic stacks and a point `x ∈ |X|`, the
induced map of automorphism group algebraic spaces `G_p ⟶ G_{p ≫ f}` is an
isomorphism for some field-valued representative of `x` if and only if it is
an isomorphism for every field-valued representative of `x`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.19.4: Let `f : X ⟶ Y` be a morphism of algebraic stacks. Let
`x ∈ |X|` be a point. The following are equivalent: for some morphism
`Spec(k) ⟶ X` in the class of `x`, setting `y = f ∘ x`, the map `G_x ⟶ G_y`
of automorphism group algebraic spaces is an isomorphism; and for any such
morphism the map of automorphism group algebraic spaces is an isomorphism. -/
@[stacks 0DTV]
theorem automorphismGroup_isIsoMap_exists_iff_forall {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y]
    (f : X ⟶ Y) (x : |X|) :
    (∃ p : FieldValuedPoint X, Points.mk p = x ∧ automorphismGroup.IsIsoMap f p) ↔
      (∀ p : FieldValuedPoint X, Points.mk p = x →
        automorphismGroup.IsIsoMap f p) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
