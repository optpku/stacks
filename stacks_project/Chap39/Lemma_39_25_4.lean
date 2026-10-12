/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Effectivity.Radicial
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

/- Lemma 39.25.4: every descent datum along a surjective finite locally free radicial
morphism of schemes is effective. -/
@[stacks 0H8L] #check
  (AlgebraicGeometry.Scheme.DescentData.IsEffective.ofFiniteLocallyFreeRadicial :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f] [IsFiniteLocallyFree f]
      [Radicial f] (D : Scheme.DescentData (fun _ : PUnit.{1} ↦ X) (fun _ ↦ f)),
      D.IsEffective)
