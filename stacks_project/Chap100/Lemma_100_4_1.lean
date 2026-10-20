module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.AlgebraicStack.FieldValuedPoint

/-!
# Equivalence of field-valued points of an algebraic stack

The 2-commutative common-extension relation on morphisms from spectra of fields
into an algebraic stack is an equivalence relation.
-/

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 100.4.1: the common-field-extension relation on morphisms from spectra
of fields into an algebraic stack is an equivalence relation. -/
@[stacks 04XF] #check
  (AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.equivalent_isEquivalence :
    {S : Scheme.{u}} → (X : GroupoidsOver S) → [AlgebraicStack X] →
      _root_.Equivalence
        (AlgebraicGeometry.AlgebraicStack.FieldValuedPoint.Equivalent :
          AlgebraicGeometry.AlgebraicStack.FieldValuedPoint X →
            AlgebraicGeometry.AlgebraicStack.FieldValuedPoint X → Prop))
