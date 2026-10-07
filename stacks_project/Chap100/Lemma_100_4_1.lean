module

public import stacks_project.Chap100.Lemma_100_4_1_FieldValuedPoint

/-!
# Equivalence of field-valued points of an algebraic stack

The 2-commutative common-extension relation on morphisms from spectra of fields
into an algebraic stack is an equivalence relation.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicStack

/-- Lemma 100.4.1: the relation of admitting a 2-commutative common field extension
is an equivalence relation on morphisms from spectra of fields into an algebraic
stack `X`. -/
@[stacks 04XF]
theorem FieldValuedPoint.equivalent_isEquivalence {S : Scheme.{u}}
    (X : GroupoidsOver S) [AlgebraicStack X] :
    _root_.Equivalence
      (FieldValuedPoint.Equivalent : FieldValuedPoint X → FieldValuedPoint X → Prop) :=
  sorry

end AlgebraicGeometry.AlgebraicStack
