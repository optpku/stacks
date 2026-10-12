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
open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 32.17.1: let `S` be a Nagata scheme and let `f : X ⟶ Y` be a quasi-compact morphism
of schemes locally of finite type over `S`. Then the following are equivalent: `f` is universally
closed; for every `n`, the base change
`𝔸ⁿ_Y ×_Y X ⟶ 𝔸ⁿ_Y` is a closed map; and the one-dimensional normal-curve
valuative lifting condition over `S` holds. -/
@[stacks 0GWV] #check
  (AlgebraicGeometry.NormalCurvePunctureValuativeCriterion.universallyClosed_tfae :
    ∀ {S X Y : Scheme.{u}} (pX : X ⟶ S) (pY : Y ⟶ S) (f : X ⟶ Y)
      [Scheme.Nagata S] [QuasiCompact f] [LocallyOfFiniteType pX] [LocallyOfFiniteType pY]
      (hf_over : f ≫ pY = pX),
      List.TFAE
        [ UniversallyClosed f
        , ∀ n : ℕ,
            IsClosedMap (pullback.snd f (AffineSpace (ULift.{u} (Fin n)) Y ↘ Y)).base
        , NormalCurvePunctureValuativeCriterion.Existence pX pY f
        ])
