/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Differentials.FittingIdeal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

/- Lemma 49.7.2: in a cartesian square of schemes, the closed subscheme defined by the
Kähler different after base change is isomorphic to the pullback of the original one. -/
@[stacks 0BVX] #check
  (AlgebraicGeometry.Scheme.Hom.fittingIdealSheaf_differentials_baseChangeComparison_isIso_of_isPullback :
    ∀ {Y Y' X X' : Scheme.{u}} (f : Y ⟶ X) [LocallyOfFiniteType f]
      (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X')
      (sq : IsPullback g' f' f g),
      IsIso (AlgebraicGeometry.Scheme.Hom.fittingIdealSheaf_differentials_baseChangeComparison f g g' f'
        (AlgebraicGeometry.Scheme.Hom.fittingIdealSheaf_differentials_comap_of_isPullback f g g' f' sq)))
