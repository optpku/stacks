/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.LocalAtTarget.Separated
import StacksCheckRecall

universe u

/- Lemma 35.23.6: the property `P(f)` given by “`f` is separated” is fpqc local
on the base. -/
@[stacks 02KU] #check (AlgebraicGeometry.IsSeparated.isLocalAtTargetFpqc :
  CategoryTheory.MorphismProperty.IsLocalAtTarget
    (@AlgebraicGeometry.IsSeparated :
      CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
    AlgebraicGeometry.Scheme.fpqcPrecoverage)
