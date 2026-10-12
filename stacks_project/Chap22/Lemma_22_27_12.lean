/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.DifferentialGraded.AdmissibleCone.Triangle
import StacksCheckRecall

@[expose] public section

open DifferentialGradedCategory

/- Lemma 22.27.12 (09QT): in a morphism of admissible-cone triangles, a homotopy equivalence on
the first two components forces a homotopy equivalence on the cone component. -/
@[stacks 09QT]
#check CompBoundaryAssignment.AdmissibleCone.homotopyEquivalences_coneMap

#check CompBoundaryAssignment.AdmissibleCone.homInK
