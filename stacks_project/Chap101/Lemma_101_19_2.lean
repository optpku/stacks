/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap101.Lemma_101_19_2_AutomorphismGroup

/-!
# Independence of the automorphism-group property on a point

For an algebraic stack `X` and a property of algebraic spaces over fields that
is invariant under ground field extensions, the automorphism group algebraic
space of a field-valued representative of a point `x ∈ |X|` has the property
for some representative if and only if it has the property for every
representative.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 101.19.2: Let `X` be an algebraic stack. Let `x ∈ |X|` be a point.
Let `P` be a property of algebraic spaces over fields which is invariant under
ground field extensions; for example `P(X/k) = X ⟶ Spec(k)` is finite. The
following are equivalent: for some morphism `Spec(k) ⟶ X` in the class of `x`
the automorphism group algebraic space `G` over `k` has `P`, and for any such
morphism the automorphism group algebraic space has `P`. -/
@[stacks 0DTT]
theorem automorphismGroup_has_exists_iff_forall {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] (x : |X|)
    (P : MorphismProperty (AlgebraicSpace S))
    [IsInvariantUnderGroundFieldExtension P] :
    (∃ p : FieldValuedPoint X, Points.mk p = x ∧ automorphismGroup.Has P p) ↔
      (∀ p : FieldValuedPoint X, Points.mk p = x →
        automorphismGroup.Has P p) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
