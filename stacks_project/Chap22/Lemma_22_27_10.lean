/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.AdmissibleCone
import StacksCheckRecall

@[expose] public section

open DifferentialGradedCategory

/- Lemma 22.27.10 (09QR): the chosen cone short complex has connecting morphism equal to the
shift of its defining map. -/
@[stacks 09QR]
#check CompBoundaryAssignment.AdmissibleCones.boundary_eq

#check CompBoundaryAssignment.AdmissibleCones.cone
#check CompBoundaryAssignment.AdmissibleCones.shortComplex
#check CompBoundaryAssignment.AdmissibleCones.splitting
