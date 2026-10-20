/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.ChernCharacter
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernPolynomial.Newton.Evaluation
public import ReasLib.AlgebraicGeometry.ChowCohomology.Restriction
public import ReasLib.AlgebraicGeometry.BivariantClass.OpenRestriction.Completion
public import ReasLib.AlgebraicGeometry.ChowCohomology.Completion
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.RankDecomposition
public import ReasLib.AlgebraicGeometry.ChowCohomology.ChernClass.Reanchor
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Representative.LocallyFree
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Basic
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.LinearAlgebra.TensorProduct.Map

@[expose] public section

open CategoryTheory ComplexShape TopologicalSpace
open scoped BigOperators DirectSum

noncomputable section

universe u

namespace AlgebraicGeometry.ChernClass.Complex

/-- Termwise pullback of a cochain complex of scheme modules. -/
noncomputable def pullbackComplex {X Y : Scheme.{u}} (g : Y ⟶ X)
    (K : CochainComplex X.Modules ℤ) : CochainComplex Y.Modules ℤ :=
  ((Scheme.Modules.pullback g).mapHomologicalComplex (up ℤ)).obj K

/-- The terms of the pulled-back complex are the pullbacks of the original terms. -/
theorem pullbackComplex_X {X Y : Scheme.{u}} (g : Y ⟶ X)
    (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    (pullbackComplex g K).X n = (Scheme.Modules.pullback g).obj (K.X n) := sorry

/-- Pullback preserves local boundedness above for complexes of scheme modules. -/
theorem pullbackComplex_isLocallyBoundedAbove {X Y : Scheme.{u}} (g : Y ⟶ X)
    (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K) :
    RingedSpace.CochainComplex.IsLocallyBoundedAbove (pullbackComplex g K) := sorry

/-- Pullback preserves local boundedness below for complexes of scheme modules. -/
theorem pullbackComplex_isLocallyBoundedBelow {X Y : Scheme.{u}} (g : Y ⟶ X)
    (K : CochainComplex X.Modules ℤ)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K) :
    RingedSpace.CochainComplex.IsLocallyBoundedBelow (pullbackComplex g K) := sorry

/-- Pullback preserves termwise finite local freeness of a complex. -/
theorem pullbackComplex_isFiniteLocallyFree {X Y : Scheme.{u}} (g : Y ⟶ X)
    (K : CochainComplex X.Modules ℤ)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n)) :
    ∀ n, Scheme.Modules.IsFiniteLocallyFree ((pullbackComplex g K).X n) := sorry

/-- The pointwise sequence of fiber ranks of the terms of a complex. -/
noncomputable def rankProfile {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ)
    (x : X) : ℤ → ℕ :=
  fun n ↦ Scheme.Modules.fiberFinrank (K.X n) x

/-- Evaluation of the rank profile is the fiber rank of the corresponding term. -/
theorem rankProfile_apply {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ)
    (x : X) (n : ℤ) :
    rankProfile K x n = Scheme.Modules.fiberFinrank (K.X n) x := sorry

/-- For a locally bounded termwise finite locally free complex, each exact rank-profile
locus is open and closed. -/
theorem rankProfile_isClopen {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n)) (ρ : ℤ →₀ ℕ) :
    IsClopen {x : X | rankProfile K x = (ρ : ℤ → ℕ)} := sorry

/-- The clopen locus on which every term of a complex has the prescribed rank profile. -/
noncomputable def rankProfileClopen {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n))
    (ρ : ℤ →₀ ℕ) : Clopens X :=
  ⟨{x : X | rankProfile K x = (ρ : ℤ → ℕ)},
    rankProfile_isClopen K hAbove hBelow hFree ρ⟩

/-- Membership in a rank-profile locus is equality with the prescribed profile. -/
theorem mem_rankProfileClopen {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n))
    (ρ : ℤ →₀ ℕ) (x : X) :
    x ∈ rankProfileClopen K hAbove hBelow hFree ρ ↔
      rankProfile K x = (ρ : ℤ → ℕ) := sorry

/-- The rank-profile loci cover the scheme. -/
theorem rankProfileClopen_iSup {X : Scheme.{u}} (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n)) :
    iSup (fun ρ : ℤ →₀ ℕ ↦ (rankProfileClopen K hAbove hBelow hFree ρ).toOpens) = ⊤ := sorry

/-- Distinct rank-profile loci are disjoint. -/
theorem rankProfileClopen_pairwiseDisjoint {X : Scheme.{u}}
    (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n)) :
    Pairwise (fun ρ σ : ℤ →₀ ℕ ↦
      Disjoint (rankProfileClopen K hAbove hBelow hFree ρ : Set X)
        (rankProfileClopen K hAbove hBelow hFree σ : Set X)) := sorry

/-- Restriction of the `n`-th term of a complex to one rank-profile locus. -/
noncomputable def restrictedTerm {S X : Scheme.{u}} (π : X ⟶ S)
    (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n))
    (ρ : ℤ →₀ ℕ) (n : ℤ) :
    (BivariantClass.ComponentRestriction.over (Over.mk π)
      (rankProfileClopen K hAbove hBelow hFree ρ).toOpens).left.Modules :=
  (Scheme.Modules.pullback
    (BivariantClass.ComponentRestriction.ι (Over.mk π)
      (rankProfileClopen K hAbove hBelow hFree ρ).toOpens).left).obj (K.X n)

/-- The restricted term is the ordinary module pullback along the profile-locus inclusion. -/
theorem restrictedTerm_def {S X : Scheme.{u}} (π : X ⟶ S)
    (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n))
    (ρ : ℤ →₀ ℕ) (n : ℤ) :
    restrictedTerm π K hAbove hBelow hFree ρ n =
      (Scheme.Modules.pullback
        (BivariantClass.ComponentRestriction.ι (Over.mk π)
          (rankProfileClopen K hAbove hBelow hFree ρ).toOpens).left).obj (K.X n) := sorry

/-- The formal total Chern series of one module, with the Chow degree recorded both in
the coefficient and in the formal variable. -/
noncomputable def moduleChernSeries {S X : Scheme.{u}} {δ : S → ℤ} {π : X ⟶ S}
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType π]
    (classes : Theory δ π) (Y : Over S) [LocallyOfFiniteType Y.hom]
    (E : Y.left.Modules) : PowerSeries (ChowCohomology.Nonnegative.ring δ Y.hom) :=
  PowerSeries.mk fun i ↦ ChernClass.homogeneous δ Y.hom i
    ((classes.reanchor Y).component E i)

/-- The coefficient of the module Chern series is its corresponding homogeneous class. -/
theorem moduleChernSeries_coeff {S X : Scheme.{u}} {δ : S → ℤ} {π : X ⟶ S}
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType π]
    (classes : Theory δ π) (Y : Over S) [LocallyOfFiniteType Y.hom]
    (E : Y.left.Modules) (i : ℕ) :
    PowerSeries.coeff i (moduleChernSeries classes Y E) =
      ChernClass.homogeneous δ Y.hom i ((classes.reanchor Y).component E i) := sorry

/-- The finite alternating product of termwise Chern series on one rank-profile locus. -/
noncomputable def profileTotalSeries {S X : Scheme.{u}} (δ : S → ℤ) (π : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType π]
    (classes : Theory δ π) (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n))
    (ρ : ℤ →₀ ℕ) :
    PowerSeries (ChowCohomology.Nonnegative.ring δ
      (BivariantClass.ComponentRestriction.over (Over.mk π)
        (rankProfileClopen K hAbove hBelow hFree ρ).toOpens).hom) :=
  ((ρ.support.sort (· ≤ ·)).map fun n ↦
    if Even n then
      moduleChernSeries classes
        (BivariantClass.ComponentRestriction.over (Over.mk π)
          (rankProfileClopen K hAbove hBelow hFree ρ).toOpens)
        (restrictedTerm π K hAbove hBelow hFree ρ n)
    else
      PowerSeries.invOfUnit
        (moduleChernSeries classes
          (BivariantClass.ComponentRestriction.over (Over.mk π)
            (rankProfileClopen K hAbove hBelow hFree ρ).toOpens)
          (restrictedTerm π K hAbove hBelow hFree ρ n)) 1).prod

/-- The profilewise total series is the finite product of the even term series and the
formal inverses of the odd term series. -/
theorem profileTotalSeries_def {S X : Scheme.{u}} (δ : S → ℤ) (π : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType π]
    (classes : Theory δ π) (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n))
    (ρ : ℤ →₀ ℕ) :
    profileTotalSeries δ π classes K hAbove hBelow hFree ρ =
      ((ρ.support.sort (· ≤ ·)).map fun n ↦
        if Even n then
          moduleChernSeries classes
            (BivariantClass.ComponentRestriction.over (Over.mk π)
              (rankProfileClopen K hAbove hBelow hFree ρ).toOpens)
            (restrictedTerm π K hAbove hBelow hFree ρ n)
        else
          PowerSeries.invOfUnit
            (moduleChernSeries classes
              (BivariantClass.ComponentRestriction.over (Over.mk π)
                (rankProfileClopen K hAbove hBelow hFree ρ).toOpens)
              (restrictedTerm π K hAbove hBelow hFree ρ n)) 1).prod := sorry

/-- The degree-`p` coefficient of the profilewise alternating total Chern series. -/
noncomputable def profileTotalClass {S X : Scheme.{u}} (δ : S → ℤ) (π : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType π]
    (classes : Theory δ π) (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n))
    (ρ : ℤ →₀ ℕ) (p : ℕ) :
    ChowCohomology.Nonnegative.degree δ
      (BivariantClass.ComponentRestriction.over (Over.mk π)
        (rankProfileClopen K hAbove hBelow hFree ρ).toOpens).hom p :=
  DirectSum.component ℤ ℕ
    (ChowCohomology.Nonnegative.degree δ
      (BivariantClass.ComponentRestriction.over (Over.mk π)
        (rankProfileClopen K hAbove hBelow hFree ρ).toOpens).hom) p
    (PowerSeries.coeff p (profileTotalSeries δ π classes K hAbove hBelow hFree ρ))

/-- The profilewise coefficient is obtained by projecting the matching Chow degree from
the corresponding coefficient of the alternating total series. -/
theorem profileTotalClass_def {S X : Scheme.{u}} (δ : S → ℤ) (π : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType π]
    (classes : Theory δ π) (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n))
    (ρ : ℤ →₀ ℕ) (p : ℕ) :
    profileTotalClass δ π classes K hAbove hBelow hFree ρ p =
      DirectSum.component ℤ ℕ
        (ChowCohomology.Nonnegative.degree δ
          (BivariantClass.ComponentRestriction.over (Over.mk π)
            (rankProfileClopen K hAbove hBelow hFree ρ).toOpens).hom) p
        (PowerSeries.coeff p
          (profileTotalSeries δ π classes K hAbove hBelow hFree ρ)) := sorry

/-- The integral Newton class of one finite locally free module. -/
noncomputable def moduleNewtonClass {S X : Scheme.{u}} {δ : S → ℤ} {π : X ⟶ S}
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType π]
    (classes : Theory δ π) (Y : Over S) [LocallyOfFiniteType Y.hom]
    (E : Y.left.Modules) (hE : Scheme.Modules.IsFiniteLocallyFree E) (p : ℕ) :
    ChowCohomology.Nonnegative.degree δ Y.hom p :=
  @ChernPolynomial.Newton.value S Y.left δ Y.hom _ _ _
    (classes.reanchor Y) E hE p

/-- The module Newton class is evaluation of the canonical augmented Newton polynomial. -/
theorem moduleNewtonClass_def {S X : Scheme.{u}} {δ : S → ℤ} {π : X ⟶ S}
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType π]
    (classes : Theory δ π) (Y : Over S) [LocallyOfFiniteType Y.hom]
    (E : Y.left.Modules) (hE : Scheme.Modules.IsFiniteLocallyFree E) (p : ℕ) :
    moduleNewtonClass classes Y E hE p =
      @ChernPolynomial.Newton.value S Y.left δ Y.hom _ _ _
        (classes.reanchor Y) E hE p := sorry

/-- The signed finite sum of termwise Newton classes on one rank-profile locus. -/
noncomputable def profileNewtonClass {S X : Scheme.{u}} (δ : S → ℤ) (π : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType π]
    (classes : Theory δ π) (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n))
    (ρ : ℤ →₀ ℕ) (p : ℕ) :
    ChowCohomology.Nonnegative.degree δ
      (BivariantClass.ComponentRestriction.over (Over.mk π)
        (rankProfileClopen K hAbove hBelow hFree ρ).toOpens).hom p :=
  ∑ n ∈ ρ.support,
    let Y := BivariantClass.ComponentRestriction.over (Over.mk π)
      (rankProfileClopen K hAbove hBelow hFree ρ).toOpens
    let g := (BivariantClass.ComponentRestriction.ι (Over.mk π)
      (rankProfileClopen K hAbove hBelow hFree ρ).toOpens).left
    let c := moduleNewtonClass classes Y
      (restrictedTerm π K hAbove hBelow hFree ρ n)
      (@Scheme.Modules.pullback_isFiniteLocallyFree Y.left X g (K.X n) (hFree n)) p
    if Even n then c else -c

/-- The profilewise Newton class is the finite signed sum of the termwise Newton classes. -/
theorem profileNewtonClass_def {S X : Scheme.{u}} (δ : S → ℤ) (π : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType π]
    (classes : Theory δ π) (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n))
    (ρ : ℤ →₀ ℕ) (p : ℕ) :
    profileNewtonClass δ π classes K hAbove hBelow hFree ρ p =
      ∑ n ∈ ρ.support,
        let Y := BivariantClass.ComponentRestriction.over (Over.mk π)
          (rankProfileClopen K hAbove hBelow hFree ρ).toOpens
        let g := (BivariantClass.ComponentRestriction.ι (Over.mk π)
          (rankProfileClopen K hAbove hBelow hFree ρ).toOpens).left
        let c := moduleNewtonClass classes Y
          (restrictedTerm π K hAbove hBelow hFree ρ n)
          (@Scheme.Modules.pullback_isFiniteLocallyFree Y.left X g (K.X n) (hFree n)) p
        if Even n then c else -c := sorry

/-- A rank-profile open lies in its inverse image under the identity. -/
theorem rankProfileClopen_le_identity_preimage {S X : Scheme.{u}} (π : X ⟶ S)
    (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n)) (ρ : ℤ →₀ ℕ) :
    (rankProfileClopen K hAbove hBelow hFree ρ).toOpens ≤
      (𝟙 (Over.mk π) : Over.mk π ⟶ Over.mk π).left ⁻¹ᵁ
        (rankProfileClopen K hAbove hBelow hFree ρ).toOpens := sorry

/-- Restriction of the identity morphism to a rank-profile open is its identity morphism. -/
theorem rankProfileClopen_identity_restriction {S X : Scheme.{u}} (π : X ⟶ S)
    (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n)) (ρ : ℤ →₀ ℕ) :
    BivariantClass.ComponentRestriction.hom (𝟙 (Over.mk π))
      (rankProfileClopen K hAbove hBelow hFree ρ).toOpens
      (rankProfileClopen K hAbove hBelow hFree ρ).toOpens
      (rankProfileClopen_le_identity_preimage π K hAbove hBelow hFree ρ) =
        𝟙 (BivariantClass.ComponentRestriction.over (Over.mk π)
          (rankProfileClopen K hAbove hBelow hFree ρ).toOpens) := sorry

/-- The total Chern-class family of a locally bounded termwise finite locally free complex,
obtained by gluing the alternating termwise products on its rank-profile loci. -/
noncomputable def totalClass {S X : Scheme.{u}} (δ : S → ℤ) (π : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType π]
    (classes : Theory δ π) (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n))
    (p : ℕ) : ChowCohomology.Nonnegative.degree δ π p :=
  -- Local instance justification (defeq pin): componentsEquiv requires this explicit pointwise group family definitionally.
  letI : ∀ ρ : ℤ →₀ ℕ, AddCommGroup
      (BivariantClass δ
        (BivariantClass.ComponentRestriction.hom (𝟙 (Over.mk π))
          (rankProfileClopen K hAbove hBelow hFree ρ).toOpens
          (rankProfileClopen K hAbove hBelow hFree (id ρ)).toOpens
          (rankProfileClopen_le_identity_preimage π K hAbove hBelow hFree ρ)) (p : ℤ)) :=
    fun ρ ↦ BivariantClass.pointwiseAddCommGroup δ
      (BivariantClass.ComponentRestriction.hom (𝟙 (Over.mk π))
        (rankProfileClopen K hAbove hBelow hFree ρ).toOpens
        (rankProfileClopen K hAbove hBelow hFree (id ρ)).toOpens
        (rankProfileClopen_le_identity_preimage π K hAbove hBelow hFree ρ)) (p : ℤ)
  (BivariantClass.OpenRestriction.Completion.componentsEquiv δ (𝟙 (Over.mk π)) (p : ℤ)
    (fun ρ : ℤ →₀ ℕ ↦ (rankProfileClopen K hAbove hBelow hFree ρ).toOpens)
    (fun ρ : ℤ →₀ ℕ ↦ (rankProfileClopen K hAbove hBelow hFree ρ).toOpens) id
    (rankProfileClopen_iSup K hAbove hBelow hFree)
    (rankProfileClopen_iSup K hAbove hBelow hFree)
    (rankProfileClopen_pairwiseDisjoint K hAbove hBelow hFree)
    (rankProfileClopen_pairwiseDisjoint K hAbove hBelow hFree)
    (fun ρ ↦ (rankProfileClopen K hAbove hBelow hFree ρ).isClopen)
    (fun ρ ↦ (rankProfileClopen K hAbove hBelow hFree ρ).isClopen)
    (rankProfileClopen_le_identity_preimage π K hAbove hBelow hFree)).symm
      (fun ρ ↦ (rankProfileClopen_identity_restriction π K hAbove hBelow hFree ρ).symm ▸
        profileTotalClass δ π classes K hAbove hBelow hFree ρ p)

/-- Restriction of the global total Chern component to a rank-profile locus recovers
the corresponding coefficient of the finite alternating product. -/
theorem totalClass_restrict_rankProfile {S X : Scheme.{u}} (δ : S → ℤ) (π : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType π]
    (classes : Theory δ π) (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n))
    (ρ : ℤ →₀ ℕ) (p : ℕ) :
    (BivariantClass.OpenRestriction.Completion.componentsEquiv δ (𝟙 (Over.mk π)) (p : ℤ)
      (fun σ : ℤ →₀ ℕ ↦ (rankProfileClopen K hAbove hBelow hFree σ).toOpens)
      (fun σ : ℤ →₀ ℕ ↦ (rankProfileClopen K hAbove hBelow hFree σ).toOpens) id
      (rankProfileClopen_iSup K hAbove hBelow hFree)
      (rankProfileClopen_iSup K hAbove hBelow hFree)
      (rankProfileClopen_pairwiseDisjoint K hAbove hBelow hFree)
      (rankProfileClopen_pairwiseDisjoint K hAbove hBelow hFree)
      (fun σ ↦ (rankProfileClopen K hAbove hBelow hFree σ).isClopen)
      (fun σ ↦ (rankProfileClopen K hAbove hBelow hFree σ).isClopen)
      (rankProfileClopen_le_identity_preimage π K hAbove hBelow hFree))
        (totalClass δ π classes K hAbove hBelow hFree p) ρ =
      (rankProfileClopen_identity_restriction π K hAbove hBelow hFree ρ).symm ▸
        profileTotalClass δ π classes K hAbove hBelow hFree ρ p := sorry

/-- The integral Newton-class family of a locally bounded termwise finite locally free
complex, obtained by gluing the alternating termwise sums on its rank-profile loci. -/
noncomputable def newtonClass {S X : Scheme.{u}} (δ : S → ℤ) (π : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType π]
    (classes : Theory δ π) (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n))
    (p : ℕ) : ChowCohomology.Nonnegative.degree δ π p :=
  -- Local instance justification (defeq pin): componentsEquiv requires this explicit pointwise group family definitionally.
  letI : ∀ ρ : ℤ →₀ ℕ, AddCommGroup
      (BivariantClass δ
        (BivariantClass.ComponentRestriction.hom (𝟙 (Over.mk π))
          (rankProfileClopen K hAbove hBelow hFree ρ).toOpens
          (rankProfileClopen K hAbove hBelow hFree (id ρ)).toOpens
          (rankProfileClopen_le_identity_preimage π K hAbove hBelow hFree ρ)) (p : ℤ)) :=
    fun ρ ↦ BivariantClass.pointwiseAddCommGroup δ
      (BivariantClass.ComponentRestriction.hom (𝟙 (Over.mk π))
        (rankProfileClopen K hAbove hBelow hFree ρ).toOpens
        (rankProfileClopen K hAbove hBelow hFree (id ρ)).toOpens
        (rankProfileClopen_le_identity_preimage π K hAbove hBelow hFree ρ)) (p : ℤ)
  (BivariantClass.OpenRestriction.Completion.componentsEquiv δ (𝟙 (Over.mk π)) (p : ℤ)
    (fun ρ : ℤ →₀ ℕ ↦ (rankProfileClopen K hAbove hBelow hFree ρ).toOpens)
    (fun ρ : ℤ →₀ ℕ ↦ (rankProfileClopen K hAbove hBelow hFree ρ).toOpens) id
    (rankProfileClopen_iSup K hAbove hBelow hFree)
    (rankProfileClopen_iSup K hAbove hBelow hFree)
    (rankProfileClopen_pairwiseDisjoint K hAbove hBelow hFree)
    (rankProfileClopen_pairwiseDisjoint K hAbove hBelow hFree)
    (fun ρ ↦ (rankProfileClopen K hAbove hBelow hFree ρ).isClopen)
    (fun ρ ↦ (rankProfileClopen K hAbove hBelow hFree ρ).isClopen)
    (rankProfileClopen_le_identity_preimage π K hAbove hBelow hFree)).symm
      (fun ρ ↦ (rankProfileClopen_identity_restriction π K hAbove hBelow hFree ρ).symm ▸
        profileNewtonClass δ π classes K hAbove hBelow hFree ρ p)

/-- Restriction of the global Newton class to a rank-profile locus recovers the finite
signed sum of the termwise integral Newton classes. -/
theorem newtonClass_restrict_rankProfile {S X : Scheme.{u}} (δ : S → ℤ) (π : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType π]
    (classes : Theory δ π) (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n))
    (ρ : ℤ →₀ ℕ) (p : ℕ) :
    (BivariantClass.OpenRestriction.Completion.componentsEquiv δ (𝟙 (Over.mk π)) (p : ℤ)
      (fun σ : ℤ →₀ ℕ ↦ (rankProfileClopen K hAbove hBelow hFree σ).toOpens)
      (fun σ : ℤ →₀ ℕ ↦ (rankProfileClopen K hAbove hBelow hFree σ).toOpens) id
      (rankProfileClopen_iSup K hAbove hBelow hFree)
      (rankProfileClopen_iSup K hAbove hBelow hFree)
      (rankProfileClopen_pairwiseDisjoint K hAbove hBelow hFree)
      (rankProfileClopen_pairwiseDisjoint K hAbove hBelow hFree)
      (fun σ ↦ (rankProfileClopen K hAbove hBelow hFree σ).isClopen)
      (fun σ ↦ (rankProfileClopen K hAbove hBelow hFree σ).isClopen)
      (rankProfileClopen_le_identity_preimage π K hAbove hBelow hFree))
        (newtonClass δ π classes K hAbove hBelow hFree p) ρ =
      (rankProfileClopen_identity_restriction π K hAbove hBelow hFree ρ).symm ▸
        profileNewtonClass δ π classes K hAbove hBelow hFree ρ p := sorry

/-- The Chern-character family of a locally bounded termwise finite locally free complex. -/
noncomputable def character {S X : Scheme.{u}} (δ : S → ℤ) (π : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType π]
    (classes : Theory δ π) (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n))
    (p : ℕ) : TensorProduct ℤ (ChowCohomology.Nonnegative.degree δ π p) ℚ :=
  TensorProduct.tmul ℤ (newtonClass δ π classes K hAbove hBelow hFree p)
    ((p.factorial : ℚ)⁻¹)

/-- The degree-`p` Chern-character component is the rationalized Newton class divided by `p!`. -/
theorem character_apply {S X : Scheme.{u}} (δ : S → ℤ) (π : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType π]
    (classes : Theory δ π) (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n)) (p : ℕ) :
    character δ π classes K hAbove hBelow hFree p =
      TensorProduct.tmul ℤ (newtonClass δ π classes K hAbove hBelow hFree p)
        ((p.factorial : ℚ)⁻¹) := sorry

/-- Total Chern classes of complexes commute with pullback along locally finite-type
morphisms. -/
theorem totalClass_pullback {S X Y : Scheme.{u}} (δ : S → ℤ) (π : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType π]
    (classes : Theory δ π) (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n))
    (g : Y ⟶ X) [LocallyOfFiniteType g] (p : ℕ) :
    ChowCohomology.restrictDegree δ
        (Over.homMk g : Over.mk (g ≫ π) ⟶ Over.mk π) (p : ℤ)
        (totalClass δ π classes K hAbove hBelow hFree p) =
      totalClass δ (g ≫ π) (classes.reanchor (Over.mk (g ≫ π)))
        (pullbackComplex g K) (pullbackComplex_isLocallyBoundedAbove g K hAbove)
        (pullbackComplex_isLocallyBoundedBelow g K hBelow)
        (pullbackComplex_isFiniteLocallyFree g K hFree) p := sorry

/-- Integral Newton classes of complexes commute with pullback along locally finite-type
morphisms. -/
theorem newtonClass_pullback {S X Y : Scheme.{u}} (δ : S → ℤ) (π : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType π]
    (classes : Theory δ π) (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n))
    (g : Y ⟶ X) [LocallyOfFiniteType g] (p : ℕ) :
    ChowCohomology.restrictDegree δ
        (Over.homMk g : Over.mk (g ≫ π) ⟶ Over.mk π) (p : ℤ)
        (newtonClass δ π classes K hAbove hBelow hFree p) =
      newtonClass δ (g ≫ π) (classes.reanchor (Over.mk (g ≫ π)))
        (pullbackComplex g K) (pullbackComplex_isLocallyBoundedAbove g K hAbove)
        (pullbackComplex_isLocallyBoundedBelow g K hBelow)
        (pullbackComplex_isFiniteLocallyFree g K hFree) p := sorry

/-- Degreewise pullback on rationalized Chow cohomology. -/
def characterRestriction {S X Y : Scheme.{u}} (δ : S → ℤ) (π : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType π]
    (g : Y ⟶ X) [LocallyOfFiniteType g] (p : ℕ) :
    TensorProduct ℤ (ChowCohomology.Nonnegative.degree δ π p) ℚ →ₗ[ℤ]
      TensorProduct ℤ (ChowCohomology.Nonnegative.degree δ (g ≫ π) p) ℚ :=
  TensorProduct.map
    (ChowCohomology.restrictDegree δ
      (Over.homMk g : Over.mk (g ≫ π) ⟶ Over.mk π) (p : ℤ)).toIntLinearMap
    LinearMap.id

/-- Pullback of a pure rationalized class acts on its Chow-cohomology factor. -/
theorem characterRestriction_tmul {S X Y : Scheme.{u}} (δ : S → ℤ) (π : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType π]
    (g : Y ⟶ X) [LocallyOfFiniteType g] (p : ℕ)
    (c : ChowCohomology.Nonnegative.degree δ π p) (q : ℚ) :
    characterRestriction δ π g p (TensorProduct.tmul ℤ c q) =
      TensorProduct.tmul ℤ
        (ChowCohomology.restrictDegree δ
          (Over.homMk g : Over.mk (g ≫ π) ⟶ Over.mk π) (p : ℤ) c) q := sorry

/-- Chern characters of complexes commute with pullback along locally finite-type
morphisms. -/
theorem character_pullback {S X Y : Scheme.{u}} (δ : S → ℤ) (π : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType π]
    (classes : Theory δ π) (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n))
    (g : Y ⟶ X) [LocallyOfFiniteType g] (p : ℕ) :
    characterRestriction δ π g p (character δ π classes K hAbove hBelow hFree p) =
      character δ (g ≫ π) (classes.reanchor (Over.mk (g ≫ π)))
        (pullbackComplex g K) (pullbackComplex_isLocallyBoundedAbove g K hAbove)
        (pullbackComplex_isLocallyBoundedBelow g K hBelow)
        (pullbackComplex_isFiniteLocallyFree g K hFree) p := sorry

/-- For a bounded complex with a fixed finite rank profile, the global total Chern
component is the coefficient of the finite alternating product of its termwise series. -/
theorem totalClass_of_bounded_constantRank
    {S X : Scheme.{u}} (δ : S → ℤ) (π : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType π]
    (classes : Theory δ π) (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n))
    (hBounded : CochainComplex.bounded X.Modules K) (ρ : ℤ →₀ ℕ)
    (hRank : ∀ n, Scheme.Modules.IsFiniteLocallyFreeOfRank (ρ n) (K.X n)) (p : ℕ) :
    totalClass δ π classes K hAbove hBelow hFree p =
      DirectSum.component ℤ ℕ (ChowCohomology.Nonnegative.degree δ π) p
        (PowerSeries.coeff p (List.prod ((ρ.support.sort (· ≤ ·)).map fun n ↦
          if Even n then moduleChernSeries classes (Over.mk π) (K.X n)
          else PowerSeries.invOfUnit
            (moduleChernSeries classes (Over.mk π) (K.X n)) 1))) := sorry

/-- For a bounded complex with a fixed finite rank profile, its integral Newton class
is the finite alternating sum of the termwise Newton classes. -/
theorem newtonClass_of_bounded_constantRank
    {S X : Scheme.{u}} (δ : S → ℤ) (π : X ⟶ S)
    [UniversallyCatenary S] [IsDimensionFunction δ] [LocallyOfFiniteType π]
    (classes : Theory δ π) (K : CochainComplex X.Modules ℤ)
    (hAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n))
    (hBounded : CochainComplex.bounded X.Modules K) (ρ : ℤ →₀ ℕ)
    (hRank : ∀ n, Scheme.Modules.IsFiniteLocallyFreeOfRank (ρ n) (K.X n)) (p : ℕ) :
    newtonClass δ π classes K hAbove hBelow hFree p =
      ∑ n ∈ ρ.support,
        if Even n then moduleNewtonClass classes (Over.mk π) (K.X n) (hFree n) p
        else -moduleNewtonClass classes (Over.mk π) (K.X n) (hFree n) p := sorry

/-- The total Chern-class families of two locally bounded, termwise finite locally free
complexes representing the same derived module are equal. -/
theorem totalClass_eq_of_representatives
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : ChernClass.Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (K L : CochainComplex X.Modules ℤ)
    (hKAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hKBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hKFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n))
    (hKRep : IsIsomorphic (DerivedCategory.Q.obj K) E)
    (hLAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove L)
    (hLBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow L)
    (hLFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (L.X n))
    (hLRep : IsIsomorphic (DerivedCategory.Q.obj L) E) :
    totalClass δ π classes K hKAbove hKBelow hKFree =
      totalClass δ π classes L hLAbove hLBelow hLFree := sorry

/-- The Chern-character families of two locally bounded, termwise finite locally free
complexes representing the same derived module are equal. -/
theorem character_eq_of_representatives
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : ChernClass.Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (K L : CochainComplex X.Modules ℤ)
    (hKAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hKBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hKFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n))
    (hKRep : IsIsomorphic (DerivedCategory.Q.obj K) E)
    (hLAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove L)
    (hLBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow L)
    (hLFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (L.X n))
    (hLRep : IsIsomorphic (DerivedCategory.Q.obj L) E) :
    character δ π classes K hKAbove hKBelow hKFree =
      character δ π classes L hLAbove hLBelow hLFree := sorry

/-- The integral degree-`p` Newton classes of two locally bounded, termwise finite locally
free complexes representing the same derived module are equal. -/
theorem newtonClass_eq_of_representatives
    {S X : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (π : X ⟶ S) [LocallyOfFiniteType π] (classes : ChernClass.Theory δ π)
    (E : RingedSpace.ModuleDerived X.toRingedSpace)
    (K L : CochainComplex X.Modules ℤ)
    (hKAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove K)
    (hKBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow K)
    (hKFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (K.X n))
    (hKRep : IsIsomorphic (DerivedCategory.Q.obj K) E)
    (hLAbove : RingedSpace.CochainComplex.IsLocallyBoundedAbove L)
    (hLBelow : RingedSpace.CochainComplex.IsLocallyBoundedBelow L)
    (hLFree : ∀ n, Scheme.Modules.IsFiniteLocallyFree (L.X n))
    (hLRep : IsIsomorphic (DerivedCategory.Q.obj L) E) (p : ℕ) :
    newtonClass δ π classes K hKAbove hKBelow hKFree p =
      newtonClass δ π classes L hLAbove hLBelow hLFree p := sorry

end AlgebraicGeometry.ChernClass.Complex
