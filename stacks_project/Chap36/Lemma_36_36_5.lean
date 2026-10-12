/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.ResolutionProperty.FiniteLocallyFree
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 36.36.5: a surjective finite locally free morphism transfers the resolution
property from its source to its target. -/
@[stacks 0GTC] #check
  (AlgebraicGeometry.Scheme.hasResolutionProperty_of_surjective_finiteLocallyFree :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Surjective f]
      [AlgebraicGeometry.IsFiniteLocallyFree f],
      AlgebraicGeometry.Scheme.HasResolutionProperty X →
        AlgebraicGeometry.Scheme.HasResolutionProperty Y)
