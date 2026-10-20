module

import ReasLib.AlgebraicGeometry.AlgebraicStack.LimitPreserving
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry FiberedCategoryOver.Groupoids
open scoped Bicategory

universe u

/- Lemma 98.11.3: let `S` be a scheme and let `X` be an algebraic stack over
`S`. The following are equivalent: `X` is a stack in setoids and
`X ⟶ (Sch/S)_fppf` is limit preserving on objects; `X` is a stack in setoids
and limit preserving; `X` is representable by an algebraic space locally of
finite presentation over `S`. -/
@[stacks 07XN] #check
  (AlgebraicGeometry.AlgebraicStack.inSetoids_limitPreserving_tfae :
    ∀ {S : Scheme.{u}} (X : GroupoidsOver S) [AlgebraicStack X],
    List.TFAE
      [IsStack.InSetoids (Scheme.fppfTopology.over S) X.p ∧
          Groupoids.Hom.LimitPreservingOnObjects
            (baseProjection.{u + 1, u, u + 1} X),
        IsStack.InSetoids (Scheme.fppfTopology.over S) X.p ∧
          Groupoids.LimitPreserving X,
        ∃ F : AlgebraicSpace S,
          Nonempty (X ≌ F.toGroupoids) ∧
            AlgebraicSpace.LocallyOfFinitePresentation
              (AlgebraicSpace.SchemeRealization.toBase F)])
