/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Correspondence.Graded.DegreeZero

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Correspondence

/- Compatibility bridge for consumers of the promoted graded correspondence owner. -/
#check (Graded.instGradedCategory :
  {k : Type u} → [Field k] → CategoryTheory.GradedCategory ℚ (Graded k) ℤ)

end AlgebraicGeometry.Correspondence
