module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.FixedRank
public import ReasLib.AlgebraicGeometry.ChowCohomology.Completion
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiniteLocallyFree.RankLocus
public import Mathlib.Algebra.Group.Center

/-!
# Chern classes from a rank decomposition

Operational classes on the clopen rank loci of a finite locally free module
glue degreewise to global classes.  Rankwise finite sums also define elements
of completed Chow cohomology, without a global bound on the occurring ranks.
-/

@[expose] public section

open CategoryTheory TopologicalSpace
open scoped DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass

/-- The degree-`i` bivariant class on the locus where `E` has rank `r`. -/
abbrev RankComponentClass
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree] (r i : ℕ) : Type (u + 1) :=
  ChowCohomology.Nonnegative.degree δ
    (BivariantClass.ComponentRestriction.over (Over.mk π)
      (Scheme.Modules.rankClopen E r).toOpens).hom i

/-- Each rank open is preserved by the identity morphism of `Over.mk π`. -/
theorem rankClopen_le_identity_preimage
    {S X : Scheme.{u}} (π : X ⟶ S)
    (E : X.Modules) [E.IsFiniteLocallyFree] (r : ℕ) :
    (Scheme.Modules.rankClopen E r).toOpens ≤
      (𝟙 (Over.mk π) : Over.mk π ⟶ Over.mk π).left ⁻¹ᵁ
        (Scheme.Modules.rankClopen E r).toOpens := sorry

/-- Restricting the identity of `Over.mk π` to a rank locus gives the identity
of that open component. -/
theorem rankClopen_identity_restriction
    {S X : Scheme.{u}} (π : X ⟶ S)
    (E : X.Modules) [E.IsFiniteLocallyFree] (r : ℕ) :
    BivariantClass.ComponentRestriction.hom (𝟙 (Over.mk π))
      (Scheme.Modules.rankClopen E r).toOpens
      (Scheme.Modules.rankClopen E r).toOpens
      (rankClopen_le_identity_preimage π E r) =
        𝟙 (BivariantClass.ComponentRestriction.over (Over.mk π)
          (Scheme.Modules.rankClopen E r).toOpens) := sorry

/-- Assemble a finite family of homogeneous classes on every rank locus into
completed Chow cohomology. -/
noncomputable def totalOfRankComponents
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree]
    (c : (r : ℕ) → (i : Fin (r + 1)) → RankComponentClass δ π E r i) :
    ChowCohomology.completedRing δ (Over.mk π)
      (fun r : ℕ ↦ (Scheme.Modules.rankClopen E r).toOpens)
      (Scheme.Modules.rankClopen_iSup E)
      (Scheme.Modules.rankClopen_pairwiseDisjoint E)
      (fun r ↦ (Scheme.Modules.rankClopen E r).isClopen)
      (rankClopen_le_identity_preimage π E) :=
  fun r ↦ ∑ i : Fin (r + 1),
    DirectSum.of (RankComponentClass δ π E r) (i : ℕ) (c r i)

/-- The degree-`i` coefficient on the rank-`r` locus is the supplied class for
`i ≤ r` and is zero above the rank. -/
theorem totalOfRankComponents_coeff
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree]
    (c : (r : ℕ) → (i : Fin (r + 1)) → RankComponentClass δ π E r i)
    (r i : ℕ) :
    totalOfRankComponents δ π E c r i =
      if h : i < r + 1 then c r ⟨i, h⟩ else 0 := sorry

/-- Glue rankwise degree-`i` operations to a global homogeneous bivariant class. -/
noncomputable def ofRankComponents
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree]
    (c : (r : ℕ) → (i : Fin (r + 1)) → RankComponentClass δ π E r i) (i : ℕ) :
    ChowCohomology.Nonnegative.degree δ π i :=
  ((BivariantClass.OpenRestriction.Completion.globalEquiv δ (𝟙 (Over.mk π))
      (fun r : ℕ ↦ (Scheme.Modules.rankClopen E r).toOpens)
      (fun r : ℕ ↦ (Scheme.Modules.rankClopen E r).toOpens) id
      (Scheme.Modules.rankClopen_iSup E) (Scheme.Modules.rankClopen_iSup E)
      (Scheme.Modules.rankClopen_pairwiseDisjoint E)
      (Scheme.Modules.rankClopen_pairwiseDisjoint E)
      (fun r ↦ (Scheme.Modules.rankClopen E r).isClopen)
      (fun r ↦ (Scheme.Modules.rankClopen E r).isClopen)
      (rankClopen_le_identity_preimage π E))
    (Eq.mp
      (ChowCohomology.completedRing_eq_completion δ (Over.mk π)
        (fun r : ℕ ↦ (Scheme.Modules.rankClopen E r).toOpens)
        (Scheme.Modules.rankClopen_iSup E)
        (Scheme.Modules.rankClopen_pairwiseDisjoint E)
        (fun r ↦ (Scheme.Modules.rankClopen E r).isClopen)
        (rankClopen_le_identity_preimage π E))
      (totalOfRankComponents δ π E c))).1 i

/-- Restriction of `ofRankComponents` recovers the supplied fixed-rank class
and vanishes in degrees above the rank. -/
theorem ofRankComponents_component
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree]
    (c : (r : ℕ) → (i : Fin (r + 1)) → RankComponentClass δ π E r i)
    (i r : ℕ) :
    (BivariantClass.OpenRestriction.Completion.componentsEquiv δ (𝟙 (Over.mk π)) (i : ℤ)
      (fun r : ℕ ↦ (Scheme.Modules.rankClopen E r).toOpens)
      (fun r : ℕ ↦ (Scheme.Modules.rankClopen E r).toOpens) id
      (Scheme.Modules.rankClopen_iSup E) (Scheme.Modules.rankClopen_iSup E)
      (Scheme.Modules.rankClopen_pairwiseDisjoint E)
      (Scheme.Modules.rankClopen_pairwiseDisjoint E)
      (fun r ↦ (Scheme.Modules.rankClopen E r).isClopen)
      (fun r ↦ (Scheme.Modules.rankClopen E r).isClopen)
      (rankClopen_le_identity_preimage π E)) (ofRankComponents δ π E c i) r =
        if h : i < r + 1 then
          (rankClopen_identity_restriction π E r).symm ▸ c r ⟨i, h⟩
        else
          BivariantClass.pointwiseZero δ
            (BivariantClass.ComponentRestriction.hom (𝟙 (Over.mk π))
              (Scheme.Modules.rankClopen E r).toOpens
              (Scheme.Modules.rankClopen E r).toOpens
              (rankClopen_le_identity_preimage π E r)) (i : ℤ) := sorry

/-- The rank operation is the degree-zero scalar `r` on the rank-`r` locus. -/
noncomputable def rankClass
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree] :
    ChowCohomology.Nonnegative.degree δ π 0 :=
  ((BivariantClass.OpenRestriction.Completion.globalEquiv δ (𝟙 (Over.mk π))
      (fun r : ℕ ↦ (Scheme.Modules.rankClopen E r).toOpens)
      (fun r : ℕ ↦ (Scheme.Modules.rankClopen E r).toOpens) id
      (Scheme.Modules.rankClopen_iSup E) (Scheme.Modules.rankClopen_iSup E)
      (Scheme.Modules.rankClopen_pairwiseDisjoint E)
      (Scheme.Modules.rankClopen_pairwiseDisjoint E)
      (fun r ↦ (Scheme.Modules.rankClopen E r).isClopen)
      (fun r ↦ (Scheme.Modules.rankClopen E r).isClopen)
      (rankClopen_le_identity_preimage π E))
    (Eq.mp
      (ChowCohomology.completedRing_eq_completion δ (Over.mk π)
        (fun r : ℕ ↦ (Scheme.Modules.rankClopen E r).toOpens)
        (Scheme.Modules.rankClopen_iSup E)
        (Scheme.Modules.rankClopen_pairwiseDisjoint E)
        (fun r ↦ (Scheme.Modules.rankClopen E r).isClopen)
        (rankClopen_le_identity_preimage π E))
      ((fun r ↦ DirectSum.of (RankComponentClass δ π E r) 0
          (ChowCohomology.Nonnegative.natCast δ
            (BivariantClass.ComponentRestriction.over (Over.mk π)
              (Scheme.Modules.rankClopen E r).toOpens).hom r)) :
        ChowCohomology.completedRing δ (Over.mk π)
          (fun r : ℕ ↦ (Scheme.Modules.rankClopen E r).toOpens)
          (Scheme.Modules.rankClopen_iSup E)
          (Scheme.Modules.rankClopen_pairwiseDisjoint E)
          (fun r ↦ (Scheme.Modules.rankClopen E r).isClopen)
          (rankClopen_le_identity_preimage π E)))).1 0

/-- On the rank-`r` component, `rankClass` is the degree-zero scalar `r`. -/
theorem rankClass_component
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree] (r : ℕ) :
    (BivariantClass.OpenRestriction.Completion.componentsEquiv δ (𝟙 (Over.mk π)) 0
      (fun r : ℕ ↦ (Scheme.Modules.rankClopen E r).toOpens)
      (fun r : ℕ ↦ (Scheme.Modules.rankClopen E r).toOpens) id
      (Scheme.Modules.rankClopen_iSup E) (Scheme.Modules.rankClopen_iSup E)
      (Scheme.Modules.rankClopen_pairwiseDisjoint E)
      (Scheme.Modules.rankClopen_pairwiseDisjoint E)
      (fun r ↦ (Scheme.Modules.rankClopen E r).isClopen)
      (fun r ↦ (Scheme.Modules.rankClopen E r).isClopen)
      (rankClopen_le_identity_preimage π E)) (rankClass δ π E) r =
        (rankClopen_identity_restriction π E r).symm ▸
          ChowCohomology.Nonnegative.natCast δ
            (BivariantClass.ComponentRestriction.over (Over.mk π)
              (Scheme.Modules.rankClopen E r).toOpens).hom r := sorry

/-- Componentwise central operations glue to a central global homogeneous class. -/
theorem ofRankComponents_mem_center
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree]
    (c : (r : ℕ) → (i : Fin (r + 1)) → RankComponentClass δ π E r i)
    (hcentral : ∀ r (i : Fin (r + 1)),
      DirectSum.of
        (ChowCohomology.degree δ
          (BivariantClass.ComponentRestriction.over (Over.mk π)
            (Scheme.Modules.rankClopen E r).toOpens).hom)
        ((i : ℕ) : ℤ) (c r i) ∈
          Set.center (ChowCohomology.ring δ
            (BivariantClass.ComponentRestriction.over (Over.mk π)
              (Scheme.Modules.rankClopen E r).toOpens).hom))
    (i : ℕ) :
    DirectSum.of (ChowCohomology.degree δ π) (i : ℤ)
      (ofRankComponents δ π E c i) ∈ Set.center (ChowCohomology.ring δ π) := sorry

/-- The rank class is central in the Chow cohomology ring. -/
theorem rankClass_mem_center
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree] :
    DirectSum.of (ChowCohomology.degree δ π) (0 : ℤ) (rankClass δ π E) ∈
      Set.center (ChowCohomology.ring δ π) := sorry

/-- The canonical Chern component on the rank-`r` locus. -/
noncomputable def rankComponent
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree] (r : ℕ) (i : Fin (r + 1)) :
    RankComponentClass δ π E r i :=
  @FixedRank.component _ _ inferInstance δ inferInstance
    (BivariantClass.ComponentRestriction.over (Over.mk π)
      (Scheme.Modules.rankClopen E r).toOpens).hom inferInstance
    ((Scheme.Modules.pullback
      (Scheme.Opens.ι (Scheme.Modules.rankClopen E r).toOpens)).obj E) r
    (Scheme.Modules.rankClopenPullback_isFiniteLocallyFreeOfRank E r) i

/-- The canonical rank-locus component is the fixed-rank operational Chern class
of the restricted module. -/
theorem rankComponent_eq_fixedRank
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree] (r : ℕ) (i : Fin (r + 1)) :
    rankComponent δ π E r i =
      @FixedRank.component _ _ inferInstance δ inferInstance
        (BivariantClass.ComponentRestriction.over (Over.mk π)
          (Scheme.Modules.rankClopen E r).toOpens).hom inferInstance
        ((Scheme.Modules.pullback
          (Scheme.Opens.ι (Scheme.Modules.rankClopen E r).toOpens)).obj E) r
        (Scheme.Modules.rankClopenPullback_isFiniteLocallyFreeOfRank E r) i := sorry

/-- The degree-`i` Chern class of a finite locally free module, glued from its
canonical fixed-rank components. -/
noncomputable def chernClass
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ) :
    ChowCohomology.Nonnegative.degree δ π i :=
  ofRankComponents δ π E (rankComponent δ π E) i

/-- On the rank-`r` locus, the global Chern class is the fixed-rank component
for `i ≤ r` and vanishes above the rank. -/
theorem chernClass_component
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree] (i r : ℕ) :
    (BivariantClass.OpenRestriction.Completion.componentsEquiv δ (𝟙 (Over.mk π)) (i : ℤ)
      (fun r : ℕ ↦ (Scheme.Modules.rankClopen E r).toOpens)
      (fun r : ℕ ↦ (Scheme.Modules.rankClopen E r).toOpens) id
      (Scheme.Modules.rankClopen_iSup E) (Scheme.Modules.rankClopen_iSup E)
      (Scheme.Modules.rankClopen_pairwiseDisjoint E)
      (Scheme.Modules.rankClopen_pairwiseDisjoint E)
      (fun r ↦ (Scheme.Modules.rankClopen E r).isClopen)
      (fun r ↦ (Scheme.Modules.rankClopen E r).isClopen)
      (rankClopen_le_identity_preimage π E)) (chernClass δ π E i) r =
        if h : i < r + 1 then
          (rankClopen_identity_restriction π E r).symm ▸
            @FixedRank.component _ _ inferInstance δ inferInstance
              (BivariantClass.ComponentRestriction.over (Over.mk π)
                (Scheme.Modules.rankClopen E r).toOpens).hom inferInstance
              ((Scheme.Modules.pullback
                (Scheme.Opens.ι (Scheme.Modules.rankClopen E r).toOpens)).obj E) r
              (Scheme.Modules.rankClopenPullback_isFiniteLocallyFreeOfRank E r) ⟨i, h⟩
        else
          BivariantClass.pointwiseZero δ
            (BivariantClass.ComponentRestriction.hom (𝟙 (Over.mk π))
              (Scheme.Modules.rankClopen E r).toOpens
              (Scheme.Modules.rankClopen E r).toOpens
              (rankClopen_le_identity_preimage π E r)) (i : ℤ) := sorry

/-- The completed total Chern class, finite in degree on each rank locus. -/
noncomputable def totalChernClass
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree] :
    ChowCohomology.completedRing δ (Over.mk π)
      (fun r : ℕ ↦ (Scheme.Modules.rankClopen E r).toOpens)
      (Scheme.Modules.rankClopen_iSup E)
      (Scheme.Modules.rankClopen_pairwiseDisjoint E)
      (fun r ↦ (Scheme.Modules.rankClopen E r).isClopen)
      (rankClopen_le_identity_preimage π E) :=
  totalOfRankComponents δ π E (rankComponent δ π E)

/-- The coefficient of the completed total Chern class on a rank locus is the
corresponding fixed-rank component below the rank and zero above it. -/
theorem totalChernClass_coeff
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree] (r i : ℕ) :
    totalChernClass δ π E r i =
      if h : i < r + 1 then
        @FixedRank.component _ _ inferInstance δ inferInstance
          (BivariantClass.ComponentRestriction.over (Over.mk π)
            (Scheme.Modules.rankClopen E r).toOpens).hom inferInstance
          ((Scheme.Modules.pullback
            (Scheme.Opens.ι (Scheme.Modules.rankClopen E r).toOpens)).obj E) r
          (Scheme.Modules.rankClopenPullback_isFiniteLocallyFreeOfRank E r) ⟨i, h⟩
      else 0 := sorry

/-- Every canonical Chern class of a finite locally free module is central. -/
theorem chernClass_mem_center
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ) :
    DirectSum.of (ChowCohomology.degree δ π) (i : ℤ) (chernClass δ π E i) ∈
      Set.center (ChowCohomology.ring δ π) := sorry

end AlgebraicGeometry.ChernClass
