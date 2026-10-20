/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import ReasLib.AlgebraicGeometry.Scheme.Morphism.ValuativeCriterion.DVR.Noetherian
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 32.15.4: for a finite-type morphism to a locally Noetherian scheme, universal
closedness, closedness after every finite-dimensional relative affine-space base change,
valuative existence, and DVR-valuative existence are equivalent. -/
@[stacks 05JY] #check
  (AlgebraicGeometry.ValuativeCriterion.DVR.universallyClosed_tfae :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Scheme.Hom.FiniteType f] [IsLocallyNoetherian S],
      List.TFAE
      [ AlgebraicGeometry.UniversallyClosed f
      , ∀ n : ℕ,
          IsClosedMap (pullback.snd f (AffineSpace (ULift.{u} (Fin n)) S ↘ S)).base
      , AlgebraicGeometry.ValuativeCriterion.Existence f
      , AlgebraicGeometry.ValuativeCriterion.DVR.Existence f
      ])
