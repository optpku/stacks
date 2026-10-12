/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FormallyUnramified.BaseChange
import StacksCheckRecall

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace Limits

/- Lemma 76.14.5: A base change of a formally unramified morphism is formally
unramified. -/
@[stacks 0600] #check
  (AlgebraicGeometry.AlgebraicSpace.FormallyUnramified.instIsStableUnderBaseChange :
    ∀ {S : Scheme.{u}}, MorphismProperty.IsStableUnderBaseChange
      (@FormallyUnramified S : MorphismProperty (AlgebraicSpace S)))
