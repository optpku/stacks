/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.BivariantClass.Gysin.Total
public import ReasLib.AlgebraicGeometry.ChowGroup.Intersection.Total
public import ReasLib.AlgebraicGeometry.ChowGroup.Relative.Cycle

@[expose] public section

open CategoryTheory
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

namespace AlgebraicGeometry.ChowGroup.Total

variable {k : Type u} [Field k]

/-- Intersecting a total Chow class on a smooth scheme with the pushforward of the
fundamental class of an equidimensional regularly embedded scheme equals the pushforward
of its normal Gysin image. -/
theorem intersectionProduct_eq_pushforward_gysin
    (X : SchemeOverField k) [Smooth X.hom] {Y : SchemeOverField k} (i : Y ⟶ X)
    [IsRegularClosedImmersion i.left] (e : ℕ) [RelativeDimension Y.hom e]
    (DΔ : DiagonalSpecializationOfRankLoci X)
    (Di : BivariantClass.Gysin.NormalSpecializationOfRankLoci i)
    (alpha : Total (fun _ ↦ 0) X) :
    intersectionProductOfRankLoci X DΔ alpha
        (map (fun _ ↦ 0) i
          (DirectSum.of _ (e : ℤ) (RelativeChow.fundamentalClass (fun _ ↦ 0) Y (e : ℤ)))) =
      map (fun _ ↦ 0) i (BivariantClass.gysinMapOfRankLoci i Di alpha) := sorry

end AlgebraicGeometry.ChowGroup.Total
