/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.AffineStratification
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.AffineCover

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.AffineOpenCover

variable {X : Scheme.{u}}

/-- A scheme with a finite affine open cover is quasi-compact. -/
theorem compactSpace_of_hasCard {t : ℕ} (h_cover : HasCard X t) :
    CompactSpace X := sorry

end AlgebraicGeometry.Scheme.AffineOpenCover

namespace AlgebraicGeometry.Scheme.FiniteAffineStratification

variable {X : Scheme.{u}}

/-- An affine open cover indexed by `Fin (n + 1)` yields an attainable affine
stratification length bounded by `n`. -/
theorem exists_hasLength_le_of_hasCard [Nonempty X] [X.IsSeparated] {n : ℕ}
    (h_cover : AffineOpenCover.HasCard X (n + 1)) :
    ∃ m, m ≤ n ∧ HasLength X m := sorry

/-- For a nonempty separated scheme with an affine open cover indexed by
`Fin (n + 1)`, the affine stratification number is at most `n`. -/
theorem number_le_of_hasCard [Nonempty X] [X.IsSeparated] {n : ℕ}
    (h_cover : AffineOpenCover.HasCard X (n + 1)) :
    -- Local instance justification (proof-local temporary data): the finite affine cover supplies the compactness required by the canonical stratification number.
    letI : CompactSpace X := AffineOpenCover.compactSpace_of_hasCard h_cover
    number X ≤ n := sorry

end AlgebraicGeometry.Scheme.FiniteAffineStratification
