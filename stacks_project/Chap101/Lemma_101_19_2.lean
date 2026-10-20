module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.AutomorphismGroup
import StacksCheckRecall

/-!
# Independence of the automorphism-group property on a point

A ground-field-invariant property of automorphism algebraic spaces is
independent of the field-valued representative of a point.
-/

open CategoryTheory AlgebraicGeometry
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

/- Lemma 101.19.2: A ground-field-invariant property holds for the automorphism
group of some representative of a point exactly when it holds for every
representative. -/
@[stacks 0DTT] #check
  (AlgebraicGeometry.AlgebraicStack.automorphismGroup_has_exists_iff_forall :
    ∀ {S : Scheme.{u}}
    {X : GroupoidsOver S} [AlgebraicStack X] (x : |X|)
    (P : MorphismProperty (AlgebraicSpace S))
    [IsInvariantUnderGroundFieldExtension P],
    (∃ p : FieldValuedPoint X, Points.mk p = x ∧ automorphismGroup.Has P p) ↔
      (∀ p : FieldValuedPoint X, Points.mk p = x →
        automorphismGroup.Has P p))

end AlgebraicGeometry.AlgebraicStack
