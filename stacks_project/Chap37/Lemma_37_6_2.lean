/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyUnramified.Lifting
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 37.6.2: a formally unramified morphism admits at most one lift through a
first-order thickening, without any affineness assumptions on the thickened schemes. -/
@[stacks 04F1] #check
  (AlgebraicGeometry.FormallyUnramified.subsingleton_liftStruct :
    ∀ {X S T T' : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
      [AlgebraicGeometry.FormallyUnramified f] (i : T ⟶ T')
      [AlgebraicGeometry.IsFirstOrderThickening i] (g : T ⟶ X) (h : T' ⟶ S)
      (sq : CommSq g i f h), Subsingleton sq.LiftStruct)
