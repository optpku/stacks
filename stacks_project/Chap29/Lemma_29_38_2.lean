/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.38.2: a relatively very ample module over a quasi-compact morphism is relatively
ample. -/
@[stacks 01VN] #check
  (AlgebraicGeometry.RelativelyVeryAmple.relativelyAmple_of_quasiCompact :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} {f : X ⟶ S} {L : X.Modules}
      [AlgebraicGeometry.QuasiCompact f]
      (h : AlgebraicGeometry.RelativelyVeryAmple f L),
      AlgebraicGeometry.RelativelyAmple f L)
