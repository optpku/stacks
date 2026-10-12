/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap74.Lemma_74_11_2_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.11.2: the property `P(f)` given by “`f` is quasi-separated” is fpqc
local on the base. -/
@[stacks 041N] #check
  (AlgebraicSpace.QuasiSeparated.isLocalAtTargetFpqc :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.QuasiSeparated S : MorphismProperty (AlgebraicSpace S))
      (fpqcPrecoverage S))
