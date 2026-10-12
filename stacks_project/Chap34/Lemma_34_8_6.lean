/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Cover.Ph
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 34.8.6: if `f : Y ⟶ X` is a surjective proper morphism of schemes, then the singleton
family `{f : Y ⟶ X}` is a ph covering. -/
@[stacks 0DES] #check
  (@AlgebraicGeometry.phCoveringSingletonOfProperSurjective :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)
      [AlgebraicGeometry.IsProper f] [AlgebraicGeometry.Surjective f],
      AlgebraicGeometry.PhCovering (fun _ : PUnit ↦ Y) (fun _ : PUnit ↦ f))
