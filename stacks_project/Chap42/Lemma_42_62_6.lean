/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.Intersection.RegularImmersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open AlgebraicGeometry.Scheme.Hom

universe u

/- Lemma 42.62.6: Intersection with the fundamental class of an equidimensional regular
closed subscheme of a smooth scheme is the pushforward of its normal Gysin action. -/
@[stacks 0FFE] #check
  (AlgebraicGeometry.ChowGroup.Total.intersectionProduct_eq_pushforward_gysin :
    ∀ {k : Type u} [Field k] (X : SchemeOverField k) [Smooth X.hom]
      {Y : SchemeOverField k} (i : Y ⟶ X) [IsRegularClosedImmersion i.left]
      (e : ℕ) [RelativeDimension Y.hom e]
      (DΔ : ChowGroup.DiagonalSpecializationOfRankLoci X)
      (Di : BivariantClass.Gysin.NormalSpecializationOfRankLoci i)
      (alpha : ChowGroup.Total (fun _ ↦ 0) X),
      ChowGroup.Total.intersectionProductOfRankLoci X DΔ alpha
          (ChowGroup.Total.map (fun _ ↦ 0) i
            (DirectSum.of _ (e : ℤ)
              (RelativeChow.fundamentalClass (fun _ ↦ 0) Y (e : ℤ)))) =
        ChowGroup.Total.map (fun _ ↦ 0) i (BivariantClass.gysinMapOfRankLoci i Di alpha))
