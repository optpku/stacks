/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap74.Lemma_74_12_2_Instances
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.12.2: the property `P(f)` given by “`f` is locally separated” is fppf
local on the base. -/
@[stacks 042F] #check
  (AlgebraicSpace.LocallySeparated.isLocalAtTargetFppf :
    MorphismProperty.IsLocalAtTarget
      (@AlgebraicSpace.LocallySeparated S : MorphismProperty (AlgebraicSpace S))
      (fppfPrecoverage S))
