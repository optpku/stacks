/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.TopChern

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped DirectSum

noncomputable section

universe u

/- The degreewise rank-component assembler is available through the shared owner. -/
#check (AlgebraicGeometry.ChernClass.topDegreeOfRankComponents :
  ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree]
    (cTop : (r : ℕ) → AlgebraicGeometry.ChernClass.RankComponentClass δ π E r r)
    (r : ℕ), AlgebraicGeometry.ChowCohomology.Nonnegative.degree δ π r)

/- Restriction of the degreewise assembler is available through the shared owner. -/
#check (AlgebraicGeometry.ChernClass.topDegreeOfRankComponents_component :
  ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree]
    (cTop : (r : ℕ) → AlgebraicGeometry.ChernClass.RankComponentClass δ π E r r)
    (r s : ℕ),
    (AlgebraicGeometry.BivariantClass.OpenRestriction.Completion.componentsEquiv δ
      (𝟙 (Over.mk π)) (r : ℤ)
      (fun n : ℕ ↦ (AlgebraicGeometry.Scheme.Modules.rankClopen E n).toOpens)
      (fun n : ℕ ↦ (AlgebraicGeometry.Scheme.Modules.rankClopen E n).toOpens) id
      (AlgebraicGeometry.Scheme.Modules.rankClopen_iSup E)
      (AlgebraicGeometry.Scheme.Modules.rankClopen_iSup E)
      (AlgebraicGeometry.Scheme.Modules.rankClopen_pairwiseDisjoint E)
      (AlgebraicGeometry.Scheme.Modules.rankClopen_pairwiseDisjoint E)
      (fun n ↦ (AlgebraicGeometry.Scheme.Modules.rankClopen E n).isClopen)
      (fun n ↦ (AlgebraicGeometry.Scheme.Modules.rankClopen E n).isClopen)
      (AlgebraicGeometry.ChernClass.rankClopen_le_identity_preimage π E))
        (AlgebraicGeometry.ChernClass.topDegreeOfRankComponents δ π E cTop r) s =
      if h : s = r then
        (AlgebraicGeometry.ChernClass.rankClopen_identity_restriction π E s).symm ▸
          cast
            (congrArg
              (fun n ↦ AlgebraicGeometry.ChernClass.RankComponentClass δ π E n r)
              h.symm)
            (cTop r)
      else
        AlgebraicGeometry.BivariantClass.pointwiseZero δ
          (AlgebraicGeometry.BivariantClass.ComponentRestriction.hom (𝟙 (Over.mk π))
            (AlgebraicGeometry.Scheme.Modules.rankClopen E s).toOpens
            (AlgebraicGeometry.Scheme.Modules.rankClopen E s).toOpens
            (AlgebraicGeometry.ChernClass.rankClopen_le_identity_preimage π E s))
          (r : ℤ))

/- The completed rank-component assembler is available through the shared owner. -/
#check (AlgebraicGeometry.ChernClass.topOfRankComponents :
  ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree]
    (cTop : (r : ℕ) → AlgebraicGeometry.ChernClass.RankComponentClass δ π E r r),
    AlgebraicGeometry.ChowCohomology.completedRing δ (Over.mk π)
      (fun r : ℕ ↦ (AlgebraicGeometry.Scheme.Modules.rankClopen E r).toOpens)
      (AlgebraicGeometry.Scheme.Modules.rankClopen_iSup E)
      (AlgebraicGeometry.Scheme.Modules.rankClopen_pairwiseDisjoint E)
      (fun r ↦ (AlgebraicGeometry.Scheme.Modules.rankClopen E r).isClopen)
      (AlgebraicGeometry.ChernClass.rankClopen_le_identity_preimage π E))

/- The component formula for the completed assembler is available through the shared
owner. -/
#check (AlgebraicGeometry.ChernClass.topOfRankComponents_apply :
  ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree]
    (cTop : (r : ℕ) → AlgebraicGeometry.ChernClass.RankComponentClass δ π E r r)
    (r : ℕ),
    AlgebraicGeometry.ChernClass.topOfRankComponents δ π E cTop r =
      DirectSum.of (AlgebraicGeometry.ChernClass.RankComponentClass δ π E r) r (cTop r))
