/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.FiniteComponents
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay.DimensionFunction
public import ReasLib.AlgebraicGeometry.Scheme.Normal
import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Dimension
import ReasLib.AlgebraicGeometry.Scheme.Normal.Components.LocallyNoetherian
import ReasLib.Topology.IrreducibleComponents
import ReasLib.Topology.Specialization.Dimension.Catenary

/-!
# Generic relative-dimension strata

This file relates global clopen strata for a relative dimension function to its local behavior at
generic points and records two standard sufficient conditions for such strata to exist.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A decomposition into clopen strata on which the generic relative dimension is constant. -/
structure GenericDimensionStratification {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ] where
  /-- The clopen stratum of generic relative dimension `n`. -/
  stratum : ℤ → X.Opens
  /-- The strata cover the source scheme. -/
  iSup_stratum : iSup stratum = ⊤
  /-- Distinct strata are disjoint. -/
  pairwise_disjoint :
    Pairwise (fun m n ↦ Disjoint (stratum m : Set X) (stratum n : Set X))
  /-- Every stratum is also closed. -/
  isClopen_stratum : ∀ n, IsClopen (stratum n : Set X)
  /-- Generic points in the `n`-th stratum have relative dimension `n`. -/
  relativeDimension_eq : ∀ n ξ, ξ ∈ (stratum n).genericPointsInAmbient →
    f.relativeDimensionFunction δ ξ = n

namespace GenericDimensionStratification

/-- Construct a generic-dimension stratification from an explicit family of clopen strata. -/
def ofStrata {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ]
    (U : ℤ → X.Opens) (cover : iSup U = ⊤)
    (disjoint : Pairwise (fun m n ↦ Disjoint (U m : Set X) (U n : Set X)))
    (clopen : ∀ n, IsClopen (U n : Set X))
    (dimension : ∀ n ξ, ξ ∈ (U n).genericPointsInAmbient →
      f.relativeDimensionFunction δ ξ = n) :
    f.GenericDimensionStratification δ where
  stratum := U
  iSup_stratum := cover
  pairwise_disjoint := disjoint
  isClopen_stratum := clopen
  relativeDimension_eq := dimension

/-- The strata of a stratification built by `ofStrata` are the supplied family. -/
@[simp]
theorem ofStrata_stratum {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ]
    (U : ℤ → X.Opens) (cover : iSup U = ⊤)
    (disjoint : Pairwise (fun m n ↦ Disjoint (U m : Set X) (U n : Set X)))
    (clopen : ∀ n, IsClopen (U n : Set X))
    (dimension : ∀ n ξ, ξ ∈ (U n).genericPointsInAmbient →
      f.relativeDimensionFunction δ ξ = n) :
    (ofStrata f δ U cover disjoint clopen dimension).stratum = U := rfl

/-- The covering, disjointness, clopenness, and dimension laws of a stratification. -/
theorem spec {X S : Scheme.{u}} {f : X ⟶ S}
    [UniversallyCatenary S] [LocallyOfFiniteType f] {δ : S → ℤ} [IsDimensionFunction δ]
    (D : f.GenericDimensionStratification δ) :
    iSup D.stratum = ⊤ ∧
      Pairwise (fun m n ↦ Disjoint (D.stratum m : Set X) (D.stratum n : Set X)) ∧
      (∀ n, IsClopen (D.stratum n : Set X)) ∧
      ∀ n ξ, ξ ∈ (D.stratum n).genericPointsInAmbient →
        f.relativeDimensionFunction δ ξ = n :=
  ⟨D.iSup_stratum, D.pairwise_disjoint, D.isClopen_stratum, D.relativeDimension_eq⟩

end GenericDimensionStratification

private theorem mem_genericPointsInAmbient_iff {X : Scheme.{u}} (U : X.Opens) (ξ : X) :
    ξ ∈ U.genericPointsInAmbient ↔ ξ ∈ genericPoints X ∧ ξ ∈ U := by
  change ξ ∈ Subtype.val '' genericPoints (U : Set X) ↔ _
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨?_, z.2⟩
    let Z : irreducibleComponents X :=
      ⟨irreducibleComponent z.1, irreducibleComponent_mem_irreducibleComponents z.1⟩
    let η := genericPoints.ofComponent Z
    have hηz : η.1 ⤳ z.1 :=
      (genericPoints.isGenericPoint_ofComponent Z).specializes mem_irreducibleComponent
    let ηU : (U : Set X) := ⟨η.1, hηz.mem_open U.isOpen z.2⟩
    have hηUz : ηU ⤳ z := U.isOpenEmbedding'.isInducing.specializes_iff.mp hηz
    have heq : closure ({ηU} : Set (U : Set X)) = closure ({z} : Set (U : Set X)) :=
      Set.Subset.antisymm (hz.2 isIrreducible_singleton.closure hηUz.closure_subset)
        hηUz.closure_subset
    have hηU : ηU = z :=
      (show IsGenericPoint ηU (closure ({z} : Set (U : Set X))) from heq).eq
        isGenericPoint_closure
    exact (congrArg Subtype.val hηU) ▸ η.2
  · rintro ⟨hξ, hξU⟩
    refine ⟨⟨ξ, hξU⟩, ?_, rfl⟩
    have hpre := preimage_mem_irreducibleComponents hξ U.isOpenEmbedding'
      ⟨ξ, subset_closure (Set.mem_singleton ξ), ⟨ξ, hξU⟩, rfl⟩
    change closure ({⟨ξ, hξU⟩} : Set (U : Set X)) ∈ irreducibleComponents (U : Set X)
    rw [U.isOpenEmbedding'.isEmbedding.closure_eq_preimage_closure_image, Set.image_singleton]
    exact hpre

private theorem isOpen_genericDimensionIndices {X : Scheme.{u}} [IsLocallyNoetherian X]
    (d : X → ℤ) (n : ℤ) :
    IsOpen {x : X | ∀ ξ : genericPoints X,
      x ∈ (genericPoints.component ξ : Set X) → d ξ.1 = n} := by
  classical
  refine isOpen_iff_mem_nhds.mpr fun x hx ↦ ?_
  obtain ⟨A, hA, hxA, -⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
  letI := IsLocallyNoetherian.component_noetherian ⟨A, hA⟩
  letI : NoetherianSpace (A : Set X) := noetherianSpace_of_isAffineOpen A hA
  let xA : (A : Set X) := ⟨x, hxA⟩
  let C : Set (Set (A : Set X)) :=
    {Z | Z ∈ irreducibleComponents (A : Set X) ∧ xA ∉ Z}
  let V : Set (A : Set X) := (⋃₀ C)ᶜ
  have hV : IsOpen V := by
    rw [show V = (⋃ Z ∈ C, Z)ᶜ by simp [V, Set.sUnion_eq_biUnion]]
    exact (NoetherianSpace.finite_irreducibleComponents.subset
      (fun _ hZ ↦ hZ.1) |>.isClosed_biUnion
        (fun Z hZ ↦ isClosed_of_mem_irreducibleComponents Z hZ.1)).isOpen_compl
  have hxV : xA ∈ V := by
    rintro hxV
    obtain ⟨Z, hZ, hxZ⟩ := Set.mem_sUnion.mp hxV
    exact hZ.2 hxZ
  have hopen : IsOpen (Subtype.val '' V : Set X) := A.isOpenEmbedding'.isOpenMap V hV
  refine Filter.mem_of_superset (hopen.mem_nhds ⟨xA, hxV, rfl⟩) ?_
  rintro y ⟨yA, hyV, rfl⟩ ξ hyξ
  apply hx ξ
  let Z : Set (A : Set X) := Subtype.val ⁻¹' (genericPoints.component ξ : Set X)
  have hZ : Z ∈ irreducibleComponents (A : Set X) :=
    preimage_mem_irreducibleComponents (genericPoints.component ξ).2 A.isOpenEmbedding'
      ⟨yA.1, hyξ, yA, rfl⟩
  by_contra hxZ
  exact hyV (Set.mem_sUnion.mpr ⟨Z, ⟨hZ, hxZ⟩, hyξ⟩)

private theorem genericDimensionStrata_spec_of_membership {X : Scheme.{u}} (d : X → ℤ)
    (U : ℤ → X.Opens)
    (mem_U : ∀ x n, x ∈ U n ↔ ∀ ξ : genericPoints X,
      x ∈ (genericPoints.component ξ : Set X) → d ξ.1 = n)
    (h : ∀ x : X, ∃ n : ℤ, ∀ ξ : genericPoints X,
      x ∈ (genericPoints.component ξ : Set X) → d ξ.1 = n) :
    iSup U = ⊤ ∧
      Pairwise (fun m n ↦ Disjoint (U m : Set X) (U n : Set X)) ∧
      (∀ n, IsClopen (U n : Set X)) ∧
      ∀ n ξ, ξ ∈ (U n).genericPointsInAmbient → d ξ = n := by
  have unique (x : X) {m n : ℤ} (hm : x ∈ U m) (hn : x ∈ U n) : m = n := by
    let Z : irreducibleComponents X :=
      ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
    let ξ := genericPoints.ofComponent Z
    have hx : x ∈ (genericPoints.component ξ : Set X) := by
      simpa [ξ] using (show x ∈ (Z : Set X) from mem_irreducibleComponent)
    exact ((mem_U x m).mp hm ξ hx).symm.trans ((mem_U x n).mp hn ξ hx)
  have disjoint : Pairwise (fun m n ↦ Disjoint (U m : Set X) (U n : Set X)) := by
    intro m n hmn
    exact Set.disjoint_left.mpr fun x hxm hxn ↦ hmn (unique x hxm hxn)
  refine ⟨?_, disjoint, ?_, ?_⟩
  · apply top_unique
    intro x _
    obtain ⟨n, hn⟩ := h x
    exact Opens.mem_iSup.mpr ⟨n, (mem_U x n).mpr hn⟩
  · intro n
    refine ⟨?_, (U n).isOpen⟩
    rw [← isOpen_compl_iff]
    refine isOpen_iff_mem_nhds.mpr fun x hx ↦ ?_
    obtain ⟨m, hm⟩ := h x
    have hxm := (mem_U x m).mpr hm
    have hmn : m ≠ n := fun e ↦ hx (e ▸ hxm)
    exact Filter.mem_of_superset ((U m).isOpen.mem_nhds hxm)
      (fun y hym hyn ↦ Set.disjoint_left.mp (disjoint hmn) hym hyn)
  · intro n ξ hξ
    obtain ⟨hξ, hξU⟩ := (mem_genericPointsInAmbient_iff (U n) ξ).mp hξ
    exact (mem_U ξ n).mp hξU ⟨ξ, hξ⟩ (subset_closure (Set.mem_singleton ξ))

/-- The global clopen decomposition, local-open-neighbourhood, and
component-through-a-point descriptions of generic relative-dimension strata are equivalent. -/
theorem genericDimensionStrata_tfae {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ] :
    List.TFAE
      [ ∃ U : ℤ → X.Opens,
          iSup U = ⊤ ∧
            Pairwise (fun m n ↦ Disjoint (U m : Set X) (U n : Set X)) ∧
            (∀ n, IsClopen (U n : Set X)) ∧
            ∀ n ξ, ξ ∈ (U n).genericPointsInAmbient →
              f.relativeDimensionFunction δ ξ = n
      , ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
          ∃ n : ℤ, ∀ ξ, ξ ∈ U.genericPointsInAmbient →
            f.relativeDimensionFunction δ ξ = n
      , ∀ x : X, ∃ n : ℤ, ∀ ξ : genericPoints X,
          x ∈ (genericPoints.component ξ : Set X) →
            f.relativeDimensionFunction δ ξ.1 = n
      ] := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  refine List.tfae_of_cycle ?_ ?_
  · simp only [List.isChain_cons_cons, List.isChain_singleton, and_true]
    constructor
    · rintro ⟨U, hcover, -, -, hdim⟩ x
      obtain ⟨n, hn⟩ := (show IsOpenCover U from hcover).exists_mem x
      exact ⟨U n, hn, n, hdim n⟩
    · intro h x
      obtain ⟨U, hxU, n, hn⟩ := h x
      refine ⟨n, fun ξ hxξ ↦ hn ξ.1 ?_⟩
      exact (mem_genericPointsInAmbient_iff U ξ.1).mpr
        ⟨ξ.2, ((genericPoints.isGenericPoint ξ).specializes hxξ).mem_open U.isOpen hxU⟩
  · intro h
    let U : ℤ → X.Opens := fun n ↦
      ⟨{x | ∀ ξ : genericPoints X,
        x ∈ (genericPoints.component ξ : Set X) → f.relativeDimensionFunction δ ξ.1 = n},
        isOpen_genericDimensionIndices (f.relativeDimensionFunction δ) n⟩
    exact ⟨U, genericDimensionStrata_spec_of_membership (f.relativeDimensionFunction δ) U
      (fun _ _ ↦ Iff.rfl) h⟩

/-- A normal scheme has a clopen decomposition by its generic relative-dimension strata. -/
theorem existsGenericDimensionStrata_of_isNormal {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ]
    (hX : X.isNormal) :
    ∃ U : ℤ → X.Opens,
      iSup U = ⊤ ∧
        Pairwise (fun m n ↦ Disjoint (U m : Set X) (U n : Set X)) ∧
        (∀ n, IsClopen (U n : Set X)) ∧
        ∀ n ξ, ξ ∈ (U n).genericPointsInAmbient →
          f.relativeDimensionFunction δ ξ = n := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨ι, U, hcover, -, hU⟩ :=
    (IsLocallyNoetherian.isNormal_iff_hasPairwiseDisjointOpenCoverByNormalIntegral X).mp hX
  apply ((genericDimensionStrata_tfae f δ).out 1 0).mp
  intro x
  obtain ⟨i, hxi⟩ := hcover.exists_mem x
  letI : IsIntegral (U i).toScheme := (hU i).1
  letI : IrreducibleSpace (U i : Set X) :=
    inferInstanceAs (IrreducibleSpace (U i).toScheme)
  letI : QuasiSober (U i : Set X) := (U i).isOpenEmbedding'.quasiSober
  refine ⟨U i, hxi, f.relativeDimensionFunction δ (genericPoint (U i : Set X)).1, ?_⟩
  intro ξ hξ
  change ξ ∈ Subtype.val '' genericPoints (U i : Set X) at hξ
  obtain ⟨η, hη, rfl⟩ := hξ
  have heq : η = genericPoint (U i : Set X) := by
    rw [genericPoints_eq_singleton (α := (U i : Set X))] at hη
    exact Set.mem_singleton_iff.mp hη
  exact congrArg (fun z : (U i : Set X) ↦ f.relativeDimensionFunction δ z.1) heq

/-- A Cohen–Macaulay scheme has a clopen decomposition by its generic relative-dimension
strata. -/
theorem existsGenericDimensionStrata_of_cohenMacaulay {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f] (δ : S → ℤ) [IsDimensionFunction δ]
    [Scheme.CohenMacaulay X] :
    ∃ U : ℤ → X.Opens,
      iSup U = ⊤ ∧
        Pairwise (fun m n ↦ Disjoint (U m : Set X) (U n : Set X)) ∧
        (∀ n, IsClopen (U n : Set X)) ∧
        ∀ n ξ, ξ ∈ (U n).genericPointsInAmbient →
          f.relativeDimensionFunction δ ξ = n := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  letI : LocallyNoetherianSpace X := ⟨fun x ↦ by
    obtain ⟨A, hA, hxA, -⟩ :=
      exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
    letI := IsLocallyNoetherian.component_noetherian ⟨A, hA⟩
    exact ⟨A, hxA, noetherianSpace_of_isAffineOpen A hA⟩⟩
  have hconst := IsDimensionFunction.isLocallyConstant_sub
    (δ := f.relativeDimensionFunction δ) (δ' := Scheme.CohenMacaulay.dimensionFunction X)
    inferInstance inferInstance
  apply ((genericDimensionStrata_tfae f δ).out 1 0).mp
  intro x
  obtain ⟨U, hU, hxU, hconstU⟩ := hconst.exists_open x
  refine ⟨⟨U, hU⟩, hxU,
    f.relativeDimensionFunction δ x - Scheme.CohenMacaulay.dimensionFunction X x, ?_⟩
  intro ξ hξ
  obtain ⟨hξ, hξU⟩ := (mem_genericPointsInAmbient_iff ⟨U, hU⟩ ξ).mp hξ
  have hzero : Scheme.CohenMacaulay.dimensionFunction X ξ = 0 := by
    simp [Scheme.CohenMacaulay.dimensionFunction,
      (mem_genericPoints_iff_ringKrullDim_stalk_eq_zero ξ).mp hξ]
  have heq := hconstU ξ hξU
  change f.relativeDimensionFunction δ ξ - Scheme.CohenMacaulay.dimensionFunction X ξ = _ at heq
  simpa only [Pi.sub_apply, hzero, sub_zero] using heq

/-- An integer is a generic-dimension index at a point when every irreducible component
through that point has that generic relative dimension. -/
def IsGenericDimensionIndex {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (x : X) (n : ℤ) : Prop :=
  ∀ ξ : genericPoints X, x ∈ (genericPoints.component ξ : Set X) →
    f.relativeDimensionFunction δ ξ.1 = n

/-- A generic-dimension index specifies the relative dimension of every generic point of
an irreducible component through the given point. -/
theorem isGenericDimensionIndex_iff {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (x : X) (n : ℤ) :
    IsGenericDimensionIndex f δ x n ↔
      ∀ ξ : genericPoints X, x ∈ (genericPoints.component ξ : Set X) →
        f.relativeDimensionFunction δ ξ.1 = n := Iff.rfl

/-- A generic-dimension index of a point, when it exists, is unique. -/
theorem isGenericDimensionIndex_unique {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (x : X) {n m : ℤ}
    (hn : IsGenericDimensionIndex f δ x n)
    (hm : IsGenericDimensionIndex f δ x m) : n = m := by
  let Z : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  let ξ := genericPoints.ofComponent Z
  have hx : x ∈ (genericPoints.component ξ : Set X) := by
    simpa [ξ] using (show x ∈ (Z : Set X) from mem_irreducibleComponent)
  exact (hn ξ hx).symm.trans (hm ξ hx)

/-- The open generic-dimension index locus is the interior of the points with that index. -/
def genericDimensionIndexLocus {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (n : ℤ) : X.Opens :=
  ⟨interior {x | IsGenericDimensionIndex f δ x n}, isOpen_interior⟩

/-- If a generic-dimension index exists at every point, the index loci are disjoint clopen
strata covering the scheme, with the specified generic dimensions and index membership. -/
theorem genericDimensionIndexLoci_spec {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h : ∀ x : X, ∃ n, IsGenericDimensionIndex f δ x n) :
    iSup (genericDimensionIndexLocus f δ) = ⊤ ∧
      Pairwise (fun m n ↦ Disjoint
        (genericDimensionIndexLocus f δ m : Set X)
        (genericDimensionIndexLocus f δ n : Set X)) ∧
      (∀ n, IsClopen (genericDimensionIndexLocus f δ n : Set X)) ∧
      (∀ n ξ, ξ ∈ (genericDimensionIndexLocus f δ n).genericPointsInAmbient →
        f.relativeDimensionFunction δ ξ = n) ∧
      ∀ (x : X) (n : ℤ), x ∈ genericDimensionIndexLocus f δ n ↔
        IsGenericDimensionIndex f δ x n := by
  letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have mem_locus (x : X) (n : ℤ) :
      x ∈ genericDimensionIndexLocus f δ n ↔ IsGenericDimensionIndex f δ x n := by
    change x ∈ interior {x | ∀ ξ : genericPoints X,
      x ∈ (genericPoints.component ξ : Set X) → f.relativeDimensionFunction δ ξ.1 = n} ↔ _
    rw [(isOpen_genericDimensionIndices (f.relativeDimensionFunction δ) n).interior_eq]
    rfl
  have hspec := genericDimensionStrata_spec_of_membership (f.relativeDimensionFunction δ)
    (genericDimensionIndexLocus f δ) mem_locus h
  exact ⟨hspec.1, hspec.2.1, hspec.2.2.1, hspec.2.2.2, mem_locus⟩

namespace GenericDimensionStratification

/-- The canonical generic-dimension stratification uses the interiors of the index loci. -/
def ofPointwise {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h : ∀ x : X, ∃ n, IsGenericDimensionIndex f δ x n) :
    f.GenericDimensionStratification δ :=
  ofStrata f δ (genericDimensionIndexLocus f δ)
    (genericDimensionIndexLoci_spec f δ h).1
    (genericDimensionIndexLoci_spec f δ h).2.1
    (genericDimensionIndexLoci_spec f δ h).2.2.1
    (genericDimensionIndexLoci_spec f δ h).2.2.2.1

/-- Membership in the canonical generic-dimension stratum is the index condition. -/
theorem mem_ofPointwise {X S : Scheme.{u}} (f : X ⟶ S)
    [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ]
    (h : ∀ x : X, ∃ n, IsGenericDimensionIndex f δ x n) (x : X) (n : ℤ) :
    x ∈ (ofPointwise f δ h).stratum n ↔ IsGenericDimensionIndex f δ x n :=
  (genericDimensionIndexLoci_spec f δ h).2.2.2.2 x n

end GenericDimensionStratification

end AlgebraicGeometry.Scheme.Hom
