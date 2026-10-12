/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.PolarizedCurves.ToCurves
import StacksCheckRecall

@[expose] public section

/- Lemma 109.4.2 (1) -/
@[stacks 0DQ0] #check (AlgebraicGeometry.PolarizedCurves.instSmooth_toCurvesHom : AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Smooth AlgebraicGeometry.PolarizedCurves.toCurvesHom)

/- Lemma 109.4.2 (2) -/
@[stacks 0DQ0] #check (AlgebraicGeometry.PolarizedCurves.instSurjective_toCurvesHom : AlgebraicGeometry.AlgebraicSpace.CohStack.Hom.Surjective AlgebraicGeometry.PolarizedCurves.toCurvesHom)
