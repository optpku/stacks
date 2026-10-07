module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.RankDecomposition

/-!
# Top Chern classes from a rank decomposition

Top-degree classes on the rank loci of a finite locally free module assemble
into ordinary or completed Chow cohomology.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped BigOperators DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass

/-- The global degree-`r` class supported by the supplied top class on the rank-`r`
locus and by zero on every other rank locus. -/
noncomputable def topDegreeOfRankComponents
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree]
    (cTop : (r : ℕ) → RankComponentClass δ π E r r) (r : ℕ) :
    ChowCohomology.Nonnegative.degree δ π r :=
  ofRankComponents δ π E
    (fun s i ↦ if h : s = r ∧ (i : ℕ) = r then
      cast (congrArg₂ (RankComponentClass δ π E) h.1.symm h.2.symm) (cTop r)
    else 0) r

/-- Restriction of a rank-supported global class recovers the supplied class on the
matching rank locus and is pointwise zero on every other rank locus. -/
theorem topDegreeOfRankComponents_component
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree]
    (cTop : (r : ℕ) → RankComponentClass δ π E r r) (r s : ℕ) :
    (BivariantClass.OpenRestriction.Completion.componentsEquiv δ (𝟙 (Over.mk π)) (r : ℤ)
      (fun n : ℕ ↦ (Scheme.Modules.rankClopen E n).toOpens)
      (fun n : ℕ ↦ (Scheme.Modules.rankClopen E n).toOpens) id
      (Scheme.Modules.rankClopen_iSup E) (Scheme.Modules.rankClopen_iSup E)
      (Scheme.Modules.rankClopen_pairwiseDisjoint E)
      (Scheme.Modules.rankClopen_pairwiseDisjoint E)
      (fun n ↦ (Scheme.Modules.rankClopen E n).isClopen)
      (fun n ↦ (Scheme.Modules.rankClopen E n).isClopen)
      (rankClopen_le_identity_preimage π E))
        (topDegreeOfRankComponents δ π E cTop r) s =
      if h : s = r then
        (rankClopen_identity_restriction π E s).symm ▸
          cast (congrArg (fun n ↦ RankComponentClass δ π E n r) h.symm) (cTop r)
      else
        BivariantClass.pointwiseZero δ
          (BivariantClass.ComponentRestriction.hom (𝟙 (Over.mk π))
            (Scheme.Modules.rankClopen E s).toOpens
            (Scheme.Modules.rankClopen E s).toOpens
            (rankClopen_le_identity_preimage π E s)) (r : ℤ) := sorry

/-- Assemble one supplied top-degree class on each rank locus into completed Chow
cohomology. -/
noncomputable def topOfRankComponents
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree]
    (cTop : (r : ℕ) → RankComponentClass δ π E r r) :
    ChowCohomology.completedRing δ (Over.mk π)
      (fun r : ℕ ↦ (Scheme.Modules.rankClopen E r).toOpens)
      (Scheme.Modules.rankClopen_iSup E)
      (Scheme.Modules.rankClopen_pairwiseDisjoint E)
      (fun r ↦ (Scheme.Modules.rankClopen E r).isClopen)
      (rankClopen_le_identity_preimage π E) :=
  fun r ↦ DirectSum.of (RankComponentClass δ π E r) r (cTop r)

/-- The rank-`r` component of the completed class is the supplied degree-`r` class. -/
theorem topOfRankComponents_apply
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree]
    (cTop : (r : ℕ) → RankComponentClass δ π E r r) (r : ℕ) :
    topOfRankComponents δ π E cTop r =
      DirectSum.of (RankComponentClass δ π E r) r (cTop r) := sorry

/-- The canonical top Chern class, assembled from the degree-`r` Chern class on each
rank-`r` locus, as an element of completed Chow cohomology. -/
noncomputable def topChernClass
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree] :
    ChowCohomology.completedRing δ (Over.mk π)
      (fun r : ℕ ↦ (Scheme.Modules.rankClopen E r).toOpens)
      (Scheme.Modules.rankClopen_iSup E)
      (Scheme.Modules.rankClopen_pairwiseDisjoint E)
      (fun r ↦ (Scheme.Modules.rankClopen E r).isClopen)
      (rankClopen_le_identity_preimage π E) :=
  topOfRankComponents δ π E
    (fun r ↦ rankComponent δ π E r ⟨r, Nat.lt_succ_self r⟩)

/-- The rank-`r` component of the canonical completed top Chern class is concentrated
in degree `r` and equals the canonical Chern component on that rank locus. -/
theorem topChernClass_apply
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree] (r : ℕ) :
    topChernClass δ π E r =
      DirectSum.of (RankComponentClass δ π E r) r
        (rankComponent δ π E r ⟨r, Nat.lt_succ_self r⟩) := sorry

/-- If only finitely many rank loci are nonempty, their canonical top Chern classes
assemble as a finite sum in the full Chow cohomology ring. -/
noncomputable def finiteTopChernClass
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree]
    (hfinite : {r : ℕ | (Scheme.Modules.rankClopen E r : Set X).Nonempty}.Finite) :
    ChowCohomology.ring δ π :=
  ∑ r ∈ hfinite.toFinset,
    DirectSum.of (ChowCohomology.degree δ π) (r : ℤ)
      (topDegreeOfRankComponents δ π E
        (fun s ↦ rankComponent δ π E s ⟨s, Nat.lt_succ_self s⟩) r)

/-- The ordinary canonical top Chern class is the sum of its homogeneous classes
supported on the finitely many nonempty rank loci. -/
theorem finiteTopChernClass_eq_sum
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree]
    (hfinite : {r : ℕ | (Scheme.Modules.rankClopen E r : Set X).Nonempty}.Finite) :
    finiteTopChernClass δ π E hfinite =
      ∑ r ∈ hfinite.toFinset,
        DirectSum.of (ChowCohomology.degree δ π) (r : ℤ)
          (topDegreeOfRankComponents δ π E
            (fun s ↦ rankComponent δ π E s ⟨s, Nat.lt_succ_self s⟩) r) := sorry

end AlgebraicGeometry.ChernClass
