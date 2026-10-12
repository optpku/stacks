/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap35.Lemma_35_23_4_Instances
import StacksCheckRecall

@[expose] public section

universe u

/- Lemma 35.23.4: the property `P(f)` given by “`f` is universally open” is fpqc
local on the base. -/
@[stacks 02KT] #check (AlgebraicGeometry.UniversallyOpen.isLocalAtTargetFpqc :
  CategoryTheory.MorphismProperty.IsLocalAtTarget
    (@AlgebraicGeometry.UniversallyOpen :
      CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme.{u})
    AlgebraicGeometry.Scheme.fpqcPrecoverage)
