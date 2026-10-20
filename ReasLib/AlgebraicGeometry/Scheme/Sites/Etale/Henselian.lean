/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Sites.Coverage
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import ReasLib.RingTheory.Henselian.StrictHenselian

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

noncomputable section

namespace AlgebraicGeometry.Scheme.Etale

/-- Every étale covering of `Spec (PowerSeries ℂ)` is refined by the identity
covering. -/
theorem powerSeriesCoverRefinedByIdentity :
    ∀ (𝒰 : (Spec (.of (PowerSeries ℂ))).Cover Scheme.etalePrecoverage),
      ∃ i : 𝒰.I₀,
        ∃ s : Spec (.of (PowerSeries ℂ)) ⟶ 𝒰.X i,
          s ≫ 𝒰.f i = 𝟙 _ := sorry

/-- For a strictly henselian local ring, positive-degree cohomology on the small
étale site of its spectrum vanishes. -/
theorem strictHenselianPositiveCohomologyIsZero
    {R : Type u} [CommRing R] [StrictHenselianLocalRing R]
    [HasSheafify (Scheme.smallEtaleTopology (Spec (.of R))) AddCommGrpCat.{v}]
    [HasExt.{v} (Sheaf (Scheme.smallEtaleTopology (Spec (.of R))) AddCommGrpCat.{v})]
    (F : Sheaf (Scheme.smallEtaleTopology (Spec (.of R))) AddCommGrpCat.{v}) :
    ∀ p : ℕ, 0 < p →
      IsZero ((Sheaf.functorH (Scheme.smallEtaleTopology (Spec (.of R))) p).obj F) := sorry

end AlgebraicGeometry.Scheme.Etale
