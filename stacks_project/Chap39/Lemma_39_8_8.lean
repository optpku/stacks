module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.Center

@[expose] public section

universe u

/- Lemma 39.8.8: The center of a locally algebraic group scheme over a field is represented by
a closed subgroup scheme. -/
@[stacks 0BF8] #check
  (AlgebraicGeometry.GroupScheme.exists_center :
    ∀ {k : Type u} [Field k] (G : AlgebraicGeometry.SchemeOverField k)
      [CategoryTheory.GrpObj G] [AlgebraicGeometry.LocallyAlgebraic G],
      ∃ K : AlgebraicGeometry.Scheme.ClosedSubgroup G,
        AlgebraicGeometry.GroupScheme.IsCenter G K)
