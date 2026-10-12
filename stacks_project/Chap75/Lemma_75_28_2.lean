/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap75.Lemma_75_28_2_RelativeAmple
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 75.28.2: if `Y` is a quasi-compact quasi-separated algebraic space with the
resolution property and some invertible module on `X` is `f`-ample, then `X` has the
resolution property. -/
@[stacks 0GUT] #check
  (AlgebraicGeometry.AlgebraicSpace.hasResolutionProperty_of_exists_relativelyAmple :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.IsQuasiCompact Y]
      [AlgebraicGeometry.AlgebraicSpace.IsAbsolutelyQuasiSeparated Y],
      AlgebraicGeometry.AlgebraicSpace.HasResolutionProperty Y →
        (∃ L : X.Modules,
            CategoryTheory.MonoidalCategory.isInvertibleObject L ∧
              AlgebraicGeometry.AlgebraicSpace.RelativelyAmple f L) →
          AlgebraicGeometry.AlgebraicSpace.HasResolutionProperty X)
