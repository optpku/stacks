/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap74.Lemma_74_18_1_LocalAtSource
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicSpace

variable (S : Scheme.{u})

/- Lemma 74.18.1: the property `P(f)` given by “`f` is smooth” is smooth
local on the source. -/
@[stacks 06F2] #check
  (Smooth.isLocalAtSourceSmooth :
    MorphismProperty.IsLocalAtSource
      (@Smooth S : MorphismProperty (AlgebraicSpace S))
      (precoverage (@Smooth S)))
