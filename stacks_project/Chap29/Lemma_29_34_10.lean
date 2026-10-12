/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.UniversallyOpen
import StacksCheckRecall

universe u

/- Lemma 29.34.10: a smooth morphism is universally open. -/
@[stacks 056G] #check
  (AlgebraicGeometry.Smooth.universallyOpen :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S},
      AlgebraicGeometry.Smooth f → AlgebraicGeometry.UniversallyOpen f)
