/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Curve.Stable.SmoothLocus
import StacksCheckRecall

/-!
# Lemma 109.22.8

For `g ≥ 2`, the inclusion `|ℳ_g| ⊂ |ℳ̄_g|` is that of an open dense
subset of the canonical topology on points of the moduli stack of stable
genus-`g` curves.
-/

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 109.22.8: The inclusion of smooth genus-`g` curves in stable
 genus-`g` curves has open image for `g ≥ 2`. -/
@[stacks 0E87] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.isOpen_smoothH0OfGenusPointsSet :
    ∀ (g : ℕ) (hg : 2 ≤ g) (S : Scheme.{u}),
      IsOpen (Set.range (CohStack.Points.map
        (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.inclusionSmoothStableOfGenus g hg S))))

/- Lemma 109.22.8: The inclusion of smooth genus-`g` curves in stable
 genus-`g` curves has dense image for `g ≥ 2`. -/
@[stacks 0E87] #check
  (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.dense_smoothH0OfGenusPointsSet :
    ∀ (g : ℕ) (hg : 2 ≤ g) (S : Scheme.{u}),
      Dense (Set.range (CohStack.Points.map
        (AlgebraicGeometry.AlgebraicSpace.Spaces.Curves.inclusionSmoothStableOfGenus g hg S))))
