/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap74.Lemma_74_16_1_LocalAtSource
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.16.1: the property `P(f)` given by “`f` is locally of finite
presentation” is fppf local on the source. -/
@[stacks 06EV] #check
  (LocallyOfFinitePresentation.isLocalAtSourceFppf :
    MorphismProperty.IsLocalAtSource
      (@LocallyOfFinitePresentation S : MorphismProperty (AlgebraicSpace S))
      (fppfPrecoverage S))
