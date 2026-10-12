/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.NormalCurve.Nagata
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 32.17.2: let `S` be a Nagata scheme and let `f : X ⟶ Y` be a morphism of schemes
locally of finite type over `S`. Then `f` is separated if and only if the Nagata-base
one-dimensional normal-curve valuative uniqueness condition over `S` holds. -/
@[stacks 0GWW] #check
  (AlgebraicGeometry.NormalCurvePunctureValuativeCriterion.isSeparated_iff_uniqueness :
    ∀ {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y)
      [Scheme.Nagata S] [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
      (hf_over : f ≫ pY = pX),
      IsSeparated f ↔ NormalCurvePunctureValuativeCriterion.Uniqueness pX pY f)
