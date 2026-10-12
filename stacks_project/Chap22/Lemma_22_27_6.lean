/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.AdmissibleCone.Factorization
import StacksCheckRecall

@[expose] public section

open DifferentialGradedCategory

/- Lemma 22.27.6 (09QM): every closed morphism factors through an admissibly monic map followed
by a homotopy-retract projection. -/
@[stacks 09QM]
#check CompBoundaryAssignment.AdmissibleCones.exists_admissibleMonoFactorization

#check HomotopyRetract
#check HomotopyRetract.toHomotopyEquiv
#check HomotopyRetract.homotopyEquivalences_projection
