module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Correspondence.Graded
import ReasLib.AlgebraicGeometry.Correspondence.Graded.DegreeZero

universe u

/- Lemma 45.3.3: smooth projective schemes over a field, with rational Chow
correspondences in all degrees, form a `ℤ`-graded `ℚ`-linear category. -/
@[stacks 0FG2]
#check (AlgebraicGeometry.Correspondence.Graded.instGradedCategory :
  {k : Type u} → [Field k] →
    CategoryTheory.GradedCategory ℚ (AlgebraicGeometry.Correspondence.Graded k) ℤ)
