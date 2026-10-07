module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.RankDecomposition

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped DirectSum

noncomputable section

universe u

/- Remark 42.38.10 (1): A finite locally free module has a clopen rank-`r` locus. -/
@[stacks 0ESW] #check (AlgebraicGeometry.Scheme.Modules.rankClopen :
  ∀ {X : Scheme.{u}} (E : X.Modules) [E.IsFiniteLocallyFree] (r : ℕ), Clopens X)

/- Remark 42.38.10 (2): Membership in the rank-`r` locus is characterized by fiber rank. -/
@[stacks 0ESW] #check (AlgebraicGeometry.Scheme.Modules.mem_rankClopen :
  ∀ {X : Scheme.{u}} (E : X.Modules) [E.IsFiniteLocallyFree] (r : ℕ) (x : X),
    x ∈ AlgebraicGeometry.Scheme.Modules.rankClopen E r ↔ E.fiberFinrank x = r)

/- Remark 42.38.10 (3): The clopen rank loci cover the scheme. -/
@[stacks 0ESW] #check (AlgebraicGeometry.Scheme.Modules.rankClopen_iSup :
  ∀ {X : Scheme.{u}} (E : X.Modules) [E.IsFiniteLocallyFree],
    iSup (fun r : ℕ ↦ (AlgebraicGeometry.Scheme.Modules.rankClopen E r).toOpens) = ⊤)

/- Remark 42.38.10 (4): Distinct clopen rank loci are disjoint. -/
@[stacks 0ESW] #check (AlgebraicGeometry.Scheme.Modules.rankClopen_pairwiseDisjoint :
  ∀ {X : Scheme.{u}} (E : X.Modules) [E.IsFiniteLocallyFree],
    Pairwise (fun r s : ℕ ↦
      Disjoint (AlgebraicGeometry.Scheme.Modules.rankClopen E r : Set X)
        (AlgebraicGeometry.Scheme.Modules.rankClopen E s : Set X)))

/- Remark 42.38.10 (5): Rank loci commute with locally finite-type pullback. -/
@[stacks 0ESW] #check (AlgebraicGeometry.Scheme.Modules.rankClopen_pullback :
  ∀ {X Y : Scheme.{u}} (E : X.Modules) [E.IsFiniteLocallyFree]
    (g : Y ⟶ X) [LocallyOfFiniteType g] (r : ℕ),
    (AlgebraicGeometry.Scheme.Modules.rankClopen
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj E) r : Set Y) =
      g ⁻¹' (AlgebraicGeometry.Scheme.Modules.rankClopen E r : Set X))

/- Remark 42.38.10 (6): The canonical global Chern class restricts to the fixed-rank
operation on each rank locus and vanishes above that rank. -/
@[stacks 0ESW] #check (AlgebraicGeometry.ChernClass.chernClass_component :
  ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree] (i r : ℕ),
    (AlgebraicGeometry.BivariantClass.OpenRestriction.Completion.componentsEquiv δ
      (𝟙 (Over.mk π)) (i : ℤ)
      (fun r : ℕ ↦ (AlgebraicGeometry.Scheme.Modules.rankClopen E r).toOpens)
      (fun r : ℕ ↦ (AlgebraicGeometry.Scheme.Modules.rankClopen E r).toOpens) id
      (AlgebraicGeometry.Scheme.Modules.rankClopen_iSup E)
      (AlgebraicGeometry.Scheme.Modules.rankClopen_iSup E)
      (AlgebraicGeometry.Scheme.Modules.rankClopen_pairwiseDisjoint E)
      (AlgebraicGeometry.Scheme.Modules.rankClopen_pairwiseDisjoint E)
      (fun r ↦ (AlgebraicGeometry.Scheme.Modules.rankClopen E r).isClopen)
      (fun r ↦ (AlgebraicGeometry.Scheme.Modules.rankClopen E r).isClopen)
      (AlgebraicGeometry.ChernClass.rankClopen_le_identity_preimage π E))
        (AlgebraicGeometry.ChernClass.chernClass δ π E i) r =
      if h : i < r + 1 then
        (AlgebraicGeometry.ChernClass.rankClopen_identity_restriction π E r).symm ▸
          @AlgebraicGeometry.ChernClass.FixedRank.component _ _ inferInstance δ
            inferInstance
            (AlgebraicGeometry.BivariantClass.ComponentRestriction.over (Over.mk π)
              (AlgebraicGeometry.Scheme.Modules.rankClopen E r).toOpens).hom inferInstance
            ((AlgebraicGeometry.Scheme.Modules.pullback
              (AlgebraicGeometry.Scheme.Opens.ι
                (AlgebraicGeometry.Scheme.Modules.rankClopen E r).toOpens)).obj E)
            r (AlgebraicGeometry.Scheme.Modules.rankClopenPullback_isFiniteLocallyFreeOfRank
              E r) ⟨i, h⟩
      else
        AlgebraicGeometry.BivariantClass.pointwiseZero δ
          (AlgebraicGeometry.BivariantClass.ComponentRestriction.hom (𝟙 (Over.mk π))
            (AlgebraicGeometry.Scheme.Modules.rankClopen E r).toOpens
            (AlgebraicGeometry.Scheme.Modules.rankClopen E r).toOpens
            (AlgebraicGeometry.ChernClass.rankClopen_le_identity_preimage π E r))
          (i : ℤ))

/- Remark 42.38.10 (7): The rankwise finite Chern sums define the total Chern class
in completed Chow cohomology. -/
@[stacks 0ESW] #check (AlgebraicGeometry.ChernClass.totalChernClass :
  ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree],
    AlgebraicGeometry.ChowCohomology.completedRing δ (Over.mk π)
      (fun r : ℕ ↦ (AlgebraicGeometry.Scheme.Modules.rankClopen E r).toOpens)
      (AlgebraicGeometry.Scheme.Modules.rankClopen_iSup E)
      (AlgebraicGeometry.Scheme.Modules.rankClopen_pairwiseDisjoint E)
      (fun r ↦ (AlgebraicGeometry.Scheme.Modules.rankClopen E r).isClopen)
      (AlgebraicGeometry.ChernClass.rankClopen_le_identity_preimage π E))

/- On each rank locus, the coefficients of the total Chern class are the
fixed-rank components up to the rank and vanish above it. -/
#check (AlgebraicGeometry.ChernClass.totalChernClass_coeff :
  ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree] (r i : ℕ),
    AlgebraicGeometry.ChernClass.totalChernClass δ π E r i =
      if h : i < r + 1 then
        @AlgebraicGeometry.ChernClass.FixedRank.component _ _ inferInstance δ inferInstance
          (AlgebraicGeometry.BivariantClass.ComponentRestriction.over (Over.mk π)
            (AlgebraicGeometry.Scheme.Modules.rankClopen E r).toOpens).hom inferInstance
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (AlgebraicGeometry.Scheme.Opens.ι
              (AlgebraicGeometry.Scheme.Modules.rankClopen E r).toOpens)).obj E)
          r (AlgebraicGeometry.Scheme.Modules.rankClopenPullback_isFiniteLocallyFreeOfRank
            E r) ⟨i, h⟩
      else 0)

/- Remark 42.38.10 (8): The rank operation restricts to the scalar `r` on the
rank-`r` locus. -/
@[stacks 0ESW] #check (AlgebraicGeometry.ChernClass.rankClass_component :
  ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree] (r : ℕ),
    (AlgebraicGeometry.BivariantClass.OpenRestriction.Completion.componentsEquiv δ
      (𝟙 (Over.mk π)) 0
      (fun r : ℕ ↦ (AlgebraicGeometry.Scheme.Modules.rankClopen E r).toOpens)
      (fun r : ℕ ↦ (AlgebraicGeometry.Scheme.Modules.rankClopen E r).toOpens) id
      (AlgebraicGeometry.Scheme.Modules.rankClopen_iSup E)
      (AlgebraicGeometry.Scheme.Modules.rankClopen_iSup E)
      (AlgebraicGeometry.Scheme.Modules.rankClopen_pairwiseDisjoint E)
      (AlgebraicGeometry.Scheme.Modules.rankClopen_pairwiseDisjoint E)
      (fun r ↦ (AlgebraicGeometry.Scheme.Modules.rankClopen E r).isClopen)
      (fun r ↦ (AlgebraicGeometry.Scheme.Modules.rankClopen E r).isClopen)
      (AlgebraicGeometry.ChernClass.rankClopen_le_identity_preimage π E))
        (AlgebraicGeometry.ChernClass.rankClass δ π E) r =
      (AlgebraicGeometry.ChernClass.rankClopen_identity_restriction π E r).symm ▸
        AlgebraicGeometry.ChowCohomology.Nonnegative.natCast δ
          (AlgebraicGeometry.BivariantClass.ComponentRestriction.over (Over.mk π)
            (AlgebraicGeometry.Scheme.Modules.rankClopen E r).toOpens).hom r)

/- Remark 42.38.10 (9): Every canonical Chern class is central in Chow cohomology. -/
@[stacks 0ESW] #check (AlgebraicGeometry.ChernClass.chernClass_mem_center :
  ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree] (i : ℕ),
    DirectSum.of (AlgebraicGeometry.ChowCohomology.degree δ π) (i : ℤ)
      (AlgebraicGeometry.ChernClass.chernClass δ π E i) ∈
        Set.center (AlgebraicGeometry.ChowCohomology.ring δ π))

/- Remark 42.38.10 (10): The rank class is central in Chow cohomology. -/
@[stacks 0ESW] #check (AlgebraicGeometry.ChernClass.rankClass_mem_center :
  ∀ {S X : Scheme.{u}} [UniversallyCatenary S]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π]
    (E : X.Modules) [E.IsFiniteLocallyFree],
    DirectSum.of (AlgebraicGeometry.ChowCohomology.degree δ π) (0 : ℤ)
      (AlgebraicGeometry.ChernClass.rankClass δ π E) ∈
        Set.center (AlgebraicGeometry.ChowCohomology.ring δ π))
