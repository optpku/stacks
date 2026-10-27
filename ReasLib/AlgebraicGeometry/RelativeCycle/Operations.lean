/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Restrict
public import ReasLib.AlgebraicGeometry.CycleGroup
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Specialization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberCycleFamily

/-!
# Restriction, flat pullback, and proper pushforward of fibre cycle families

This file defines the three family-level operations on fibre cycles: restriction
to a morphism of opens, flat pullback, and proper pushforward over a common
base.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Function Set

noncomputable section

universe u

namespace AlgebraicGeometry.RelativeCycle

variable {X S : Scheme.{u}}

/-- The comparison morphism from a restricted fibre of `φ : U ⟶ V` to the original fibre of `f`. -/
noncomputable def restrictFiberMap (f : X ⟶ S) (U : X.Opens) (V : S.Opens)
    (φ : U.toScheme ⟶ V.toScheme) (hφ : φ ≫ V.ι = U.ι ≫ f) (t : V.toScheme) :
    φ.fiber t ⟶ f.fiber (V.ι t) :=
  Scheme.Hom.fiberMap φ U.ι V.ι f ⟨hφ.symm⟩ t

/-- Restricting fibre-cycle coefficients along `restrictFiberMap` has locally finite support. -/
theorem restrict_locallyFiniteSupport (f : X ⟶ S) [LocallyOfFiniteType f] {r : ℕ}
    (α : f.FiberCycleFamily r) (U : X.Opens) (V : S.Opens)
    (φ : U.toScheme ⟶ V.toScheme) (hφ : φ ≫ V.ι = U.ι ≫ f) (t : V.toScheme) :
    LocallyFiniteSupport fun x : φ.fiber t ↦
      CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction (V.ι t)) r (α (V.ι t))
        (restrictFiberMap f U V φ hφ t x) := by
  haveI : IsOpenImmersion (restrictFiberMap f U V φ hφ t) := by
    dsimp only [restrictFiberMap, Scheme.Hom.fiberMap]
    apply Scheme.pullback_map_isOpenImmersion
  intro x
  obtain ⟨W, hW, hfin⟩ :=
    (CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction (V.ι t)) r
      (α (V.ι t))).locallyFiniteSupport (restrictFiberMap f U V φ hφ t x)
  refine ⟨restrictFiberMap f U V φ hφ t ⁻¹' W,
    (restrictFiberMap f U V φ hφ t).continuous.continuousAt.preimage_mem_nhds hW, ?_⟩
  simpa only [Set.preimage_inter, Function.support, Set.preimage_setOf_eq,
    Function.locallyFinsuppWithin.toFun_eq_coe] using
    hfin.preimage (restrictFiberMap f U V φ hφ t).isEmbedding.injective.injOn

/-- The algebraic cycle on a restricted fibre obtained by restricting coefficients. -/
noncomputable def restrictCycle (f : X ⟶ S) [LocallyOfFiniteType f] {r : ℕ}
    (α : f.FiberCycleFamily r) (U : X.Opens) (V : S.Opens)
    (φ : U.toScheme ⟶ V.toScheme) (hφ : φ ≫ V.ι = U.ι ≫ f) (t : V.toScheme) :
    AlgebraicCycle (φ.fiber t) ℤ where
  toFun := fun x ↦
    CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction (V.ι t)) r (α (V.ι t))
      (restrictFiberMap f U V φ hφ t x)
  supportWithinDomain' := subset_univ _
  supportLocallyFiniteWithinDomain' := fun x _ ↦
    restrict_locallyFiniteSupport f α U V φ hφ t x

/-- Restricting a locally finite type morphism to opens in source and target preserves
local finite type. -/
theorem locallyOfFiniteType_restriction (f : X ⟶ S) [LocallyOfFiniteType f]
    (U : X.Opens) (V : S.Opens) (φ : U.toScheme ⟶ V.toScheme)
    (hφ : φ ≫ V.ι = U.ι ≫ f) : LocallyOfFiniteType φ := by
  haveI : LocallyOfFiniteType (φ ≫ V.ι) := hφ.symm ▸ inferInstance
  exact locallyOfFiniteType_of_comp φ V.ι

private theorem trdeg_le_of_ringHom_square
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Nontrivial R] [Nontrivial S] [Algebra R A] [Algebra S B]
    (f : R →+* S) (g : A →+* B) (hf : Function.Surjective f) (hg : Function.Injective g)
    (hc : (algebraMap S B).comp f = g.comp (algebraMap R A)) :
    Algebra.trdeg R A ≤ Algebra.trdeg S B := by
  rw [Algebra.trdeg]
  apply ciSup_le'
  intro s
  exact (s.property.ringHom_of_comp_eq f g hf hg hc).cardinalMk_le_trdeg

private theorem trdeg_eq_of_ringEquiv_square
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Nontrivial R] [Nontrivial S] [Algebra R A] [Algebra S B]
    (f : R ≃+* S) (g : A ≃+* B)
    (hc : (algebraMap S B).comp f.toRingHom = g.toRingHom.comp (algebraMap R A)) :
    Algebra.trdeg R A = Algebra.trdeg S B := by
  apply le_antisymm
  · exact trdeg_le_of_ringHom_square f.toRingHom g.toRingHom f.surjective g.injective hc
  · apply trdeg_le_of_ringHom_square f.symm.toRingHom g.symm.toRingHom f.symm.surjective g.symm.injective
    ext s
    apply g.injective
    simpa using (RingHom.congr_fun hc (f.symm s)).symm

private theorem residueField_trdeg_eq_of_openImmersions
    {X' Y' X Y : Scheme.{u}} (i : X' ⟶ X) [IsOpenImmersion i]
    (j : Y' ⟶ Y) [IsOpenImmersion j] (f : X ⟶ Y) (f' : X' ⟶ Y')
    (hc : i ≫ f = f' ≫ j) (x : X') :
    Algebra.trdeg (Y.residueField (f (i x))) (X.residueField (i x)) =
      Algebra.trdeg (Y'.residueField (f' x)) (X'.residueField x) := by
  let heq : f (i x) = j (f' x) := by
    simpa using congrArg (fun k : X' ⟶ Y ↦ k x) hc
  let b := (Y.residueFieldCongr heq).hom ≫ j.residueFieldMap (f' x)
  haveI : IsIso b := by
    dsimp only [b]
    infer_instance
  let eR := (asIso b).commRingCatIsoToRingEquiv
  let eA := (asIso (i.residueFieldMap x)).commRingCatIsoToRingEquiv
  apply trdeg_eq_of_ringEquiv_square eR eA
  have hmap := Scheme.Hom.residueFieldMap_congr hc x
  rw [Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp] at hmap
  exact congrArg CommRingCat.Hom.hom hmap.symm

/-- The restricted fibre cycle remains supported in dimension `r`. -/
theorem restrictCycle_mem_dimensionSubgroup (f : X ⟶ S) [LocallyOfFiniteType f]
    {r : ℕ} (α : f.FiberCycleFamily r) (U : X.Opens) (V : S.Opens)
    (φ : U.toScheme ⟶ V.toScheme) (hφ : φ ≫ V.ι = U.ι ≫ f) (t : V.toScheme) :
    restrictCycle f α U V φ hφ t ∈ AlgebraicCycle.dimensionSubgroup
      (@Scheme.Hom.fiberDimensionFunction _ _ φ
      (locallyOfFiniteType_restriction f U V φ hφ) t) r := by
  letI : LocallyOfFiniteType φ := locallyOfFiniteType_restriction f U V φ hφ
  haveI : IsOpenImmersion (restrictFiberMap f U V φ hφ t) := by
    dsimp only [restrictFiberMap, Scheme.Hom.fiberMap]
    apply Scheme.pullback_map_isOpenImmersion
  rw [AlgebraicCycle.mem_dimensionSubgroup]
  intro x hx
  have hdim := (AlgebraicCycle.mem_dimensionSubgroup _ _ _).mp (α (V.ι t)).property
    (restrictFiberMap f U V φ hφ t x) hx
  have htrdeg := residueField_trdeg_eq_of_openImmersions
    (restrictFiberMap f U V φ hφ t) (Spec.map (V.ι.residueFieldMap t))
    (f.fiberToSpecResidueField (V.ι t)) (φ.fiberToSpecResidueField t)
    (by exact pullback.lift_snd _ _ _) x
  have hdf : φ.fiberDimensionFunction t x =
      f.fiberDimensionFunction (V.ι t) (restrictFiberMap f U V φ hφ t x) := by
    simpa only [Scheme.Hom.fiberDimensionFunction, Scheme.Hom.relativeDimensionFunction,
      Scheme.Hom.residueFieldTranscendenceDegreeAt, zero_add] using
      congrArg (fun c : Cardinal ↦ ((Cardinal.toENat c).toNat : ℤ)) htrdeg.symm
  exact hdf.trans hdim

/-- Restriction of a family of fibrewise `r`-cycles to a morphism of opens over `f`. -/
noncomputable def restrict {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℕ}
    (U : X.Opens) (V : S.Opens) (φ : U.toScheme ⟶ V.toScheme)
    (hφ : φ ≫ V.ι = U.ι ≫ f) (α : f.FiberCycleFamily r) :
    @Scheme.Hom.FiberCycleFamily _ _ φ
      (locallyOfFiniteType_restriction f U V φ hφ) r :=
  fun t ↦ ⟨restrictCycle f α U V φ hφ t,
    restrictCycle_mem_dimensionSubgroup f α U V φ hφ t⟩

/-- Coefficients of a restriction are the original fibre coefficients along `restrictFiberMap`. -/
theorem restrict_apply {f : X ⟶ S} [LocallyOfFiniteType f] {r : ℕ}
    (U : X.Opens) (V : S.Opens) (φ : U.toScheme ⟶ V.toScheme)
    (hφ : φ ≫ V.ι = U.ι ≫ f) (α : f.FiberCycleFamily r) (t : V.toScheme)
    (x : φ.fiber t) :
    CycleGroup.toAlgebraicCycle (@Scheme.Hom.fiberDimensionFunction _ _ φ
      (locallyOfFiniteType_restriction f U V φ hφ) t) r
        (restrict U V φ hφ α t) x =
      CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction (V.ι t)) r (α (V.ι t))
        (restrictFiberMap f U V φ hφ t x) := rfl

/-- The comparison morphism from a fibre of `p ≫ f` to the corresponding fibre of `f`. -/
noncomputable def flatPullbackFiberMap {X' : Scheme.{u}} (f : X ⟶ S) (p : X' ⟶ X)
    (s : S) : (p ≫ f).fiber s ⟶ f.fiber s :=
  Scheme.Hom.fiberMap (p ≫ f) p (𝟙 S) f ⟨(Category.comp_id (p ≫ f)).symm⟩ s

private theorem associatedCycle_eq_zero_of_not_mem_support {T : Scheme.{u}} [IsLocallyNoetherian T]
    (Z : T.IdealSheafData) (d : T → ℤ) (k : ℤ) {x : T} (hx : x ∉ Z.support) :
    CycleGroup.toAlgebraicCycle d k (Z.associatedCycle d k) x = 0 := by
  change (∑ᶠ ξ : genericPoints Z.subscheme,
    @ite ℤ (d (Z.subschemeι ξ.1) = k) (Classical.propDecidable _)
      (Z.componentCycle ξ x) 0) = 0
  apply finsum_eq_zero_of_forall_eq_zero
  intro ξ
  have hxne : x ≠ Z.subschemeι ξ.1 := by
    intro h
    apply hx
    exact Z.range_subschemeι.subset ⟨ξ.1, h.symm⟩
  simp [Scheme.IdealSheafData.componentCycle, hxne]

private theorem pullbackPointClosures_locallyFiniteSupport
    {T U : Scheme.{u}} [IsLocallyNoetherian T] (q : T ⟶ U)
    (α : AlgebraicCycle U ℤ) (d : T → ℤ) (k : ℤ) :
    LocallyFiniteSupport (fun x : T ↦ ∑ᶠ y : U,
      α y * CycleGroup.toAlgebraicCycle d k
        (Scheme.IdealSheafData.associatedCycle
          ((Scheme.PointClosure.reducedStructure y).ideal.comap q) d k) x) := by
  classical
  let b : U → AlgebraicCycle T ℤ := fun y ↦
    CycleGroup.toAlgebraicCycle d k
      (Scheme.IdealSheafData.associatedCycle
        ((Scheme.PointClosure.reducedStructure y).ideal.comap q) d k)
  have hα : LocallyFiniteSupport (fun y ↦ α y) := by
    simpa only [Function.locallyFinsuppWithin.toFun_eq_coe] using α.locallyFiniteSupport
  intro x
  obtain ⟨W, hW, hfin⟩ := hα (q x)
  obtain ⟨W', hWsub, hWopen, hxW⟩ := mem_nhds_iff.mp hW
  obtain ⟨A, hA, hxA, hAsub⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens
      (U := ⟨q ⁻¹' W', hWopen.preimage q.continuous⟩) hxW
  refine ⟨A, A.isOpen.mem_nhds hxA, ?_⟩
  have hBfin : (W' ∩ α.support).Finite :=
    hfin.subset (Set.inter_subset_inter_left _ hWsub)
  have hfinite : (⋃ y ∈ W' ∩ α.support, (A : Set T) ∩ (b y).support).Finite := by
    apply hBfin.biUnion
    intro y _
    simpa only [Function.locallyFinsuppWithin.toFun_eq_coe] using
      (b y).locallyFiniteSupport.finite_inter_support_of_isCompact hA.isCompact
  apply hfinite.subset
  rintro z ⟨hzA, hz⟩
  have hex : ∃ y, α y * b y z ≠ 0 := by
    by_contra h
    apply hz
    apply finsum_eq_zero_of_forall_eq_zero
    simpa only [not_exists, not_not] using h
  obtain ⟨y, hy⟩ := hex
  have hyα : α y ≠ 0 := left_ne_zero_of_mul hy
  have hyb : b y z ≠ 0 := right_ne_zero_of_mul hy
  have hcl : q z ∈ closure ({y} : Set U) := by
    by_contra hzcl
    apply hyb
    apply associatedCycle_eq_zero_of_not_mem_support
    simpa [Scheme.IdealSheafData.support_comap,
      Scheme.PointClosure.reducedStructure, Scheme.ClosedSubschemeStructure.reduced,
      Scheme.IdealSheafData.support_vanishingIdeal, Scheme.PointClosure.closedSubset,
      TopologicalSpace.Closeds.preimage, TopologicalSpace.Closeds.coe_closure] using hzcl
  have hyW : y ∈ W' :=
    (specializes_iff_mem_closure.mpr hcl).mem_open hWopen (hAsub hzA)
  exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨⟨hyW, hyα⟩, ⟨hzA, hyb⟩⟩⟩

/-- Fibrewise flat-pullback coefficients have locally finite support. -/
theorem flatPullback_locallyFiniteSupport {X' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (p : X' ⟶ X) [LocallyOfFiniteType p] (e : ℕ)
    {r : ℕ} (α : f.FiberCycleFamily r) (s : S) :
    LocallyFiniteSupport fun x' : (p ≫ f).fiber s ↦
      ∑ᶠ y : f.fiber s,
        CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s) y *
          CycleGroup.toAlgebraicCycle ((p ≫ f).fiberDimensionFunction s) (r + e)
            (Scheme.IdealSheafData.associatedCycle
              ((Scheme.PointClosure.reducedStructure y).ideal.comap
                (flatPullbackFiberMap f p s))
              ((p ≫ f).fiberDimensionFunction s) (r + e)) x' := by
  exact pullbackPointClosures_locallyFiniteSupport (flatPullbackFiberMap f p s)
    (CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s))
    ((p ≫ f).fiberDimensionFunction s) (r + e)

/-- The algebraic cycle on a fibre of `p ≫ f` given by flat pullback of point closures. -/
noncomputable def flatPullbackCycle {X' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (p : X' ⟶ X) [LocallyOfFiniteType p] (e : ℕ)
    {r : ℕ} (α : f.FiberCycleFamily r) (s : S) :
    AlgebraicCycle ((p ≫ f).fiber s) ℤ where
  toFun := fun x' ↦
    ∑ᶠ y : f.fiber s,
      CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s) y *
        CycleGroup.toAlgebraicCycle ((p ≫ f).fiberDimensionFunction s) (r + e)
          (Scheme.IdealSheafData.associatedCycle
            ((Scheme.PointClosure.reducedStructure y).ideal.comap
              (flatPullbackFiberMap f p s))
            ((p ≫ f).fiberDimensionFunction s) (r + e)) x'
  supportWithinDomain' := subset_univ _
  supportLocallyFiniteWithinDomain' := fun x' _ ↦
    flatPullback_locallyFiniteSupport f p e α s x'

/-- The flat-pulled-back fibre cycle is supported in dimension `r + e`. -/
theorem flatPullbackCycle_mem_dimensionSubgroup {X' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (p : X' ⟶ X) [LocallyOfFiniteType p] (e : ℕ)
    {r : ℕ} (α : f.FiberCycleFamily r) (s : S) :
    flatPullbackCycle f p e α s ∈
      AlgebraicCycle.dimensionSubgroup ((p ≫ f).fiberDimensionFunction s) (r + e) := by
  rw [AlgebraicCycle.mem_dimensionSubgroup]
  intro x' hx'
  by_contra hdim
  apply hx'
  apply finsum_eq_zero_of_forall_eq_zero
  intro y
  have hzero :
      CycleGroup.toAlgebraicCycle ((p ≫ f).fiberDimensionFunction s) (r + e)
        (Scheme.IdealSheafData.associatedCycle
          ((Scheme.PointClosure.reducedStructure y).ideal.comap
            (flatPullbackFiberMap f p s))
          ((p ≫ f).fiberDimensionFunction s) (r + e)) x' = 0 := by
    by_contra hne
    exact hdim ((AlgebraicCycle.mem_dimensionSubgroup _ _ _).mp
      (Scheme.IdealSheafData.associatedCycle
      ((Scheme.PointClosure.reducedStructure y).ideal.comap
        (flatPullbackFiberMap f p s))
      ((p ≫ f).fiberDimensionFunction s) (r + e)).property x' hne)
  simp [hzero]

/-- Flat pullback of a family of fibrewise `r`-cycles along a flat morphism of relative dimension `e`. -/
noncomputable def flatPullback {X' : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {r : ℕ} (p : X' ⟶ X) [Flat p] (e : ℕ)
    [Scheme.Hom.RelativeDimension p e] (α : f.FiberCycleFamily r) :
    (p ≫ f).FiberCycleFamily (r + e) :=
  fun s ↦ ⟨flatPullbackCycle f p e α s,
    flatPullbackCycle_mem_dimensionSubgroup f p e α s⟩

/-- Coefficients of a flat pullback are the associated-cycle formula on the compared fibre. -/
theorem flatPullback_apply {X' : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {r : ℕ} (p : X' ⟶ X) [Flat p] (e : ℕ)
    [Scheme.Hom.RelativeDimension p e] (α : f.FiberCycleFamily r) (s : S)
    (x' : (p ≫ f).fiber s) :
    CycleGroup.toAlgebraicCycle ((p ≫ f).fiberDimensionFunction s) (r + e)
        (flatPullback p e α s) x' =
      ∑ᶠ y : f.fiber s,
        CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s) y *
          CycleGroup.toAlgebraicCycle ((p ≫ f).fiberDimensionFunction s) (r + e)
            (Scheme.IdealSheafData.associatedCycle
              ((Scheme.PointClosure.reducedStructure y).ideal.comap
                (flatPullbackFiberMap f p s))
              ((p ≫ f).fiberDimensionFunction s) (r + e)) x' := rfl

/-- The comparison morphism from a fibre of `f` to the corresponding fibre of `pY`. -/
noncomputable def pushforwardFiberMap {Y : Scheme.{u}} (f : X ⟶ S)
    (pY : Y ⟶ S) (h : X ⟶ Y) (hc : h ≫ pY = f) (s : S) :
    f.fiber s ⟶ pY.fiber s :=
  Scheme.Hom.fiberMap f h (𝟙 S) pY ⟨hc.trans (Category.comp_id f).symm⟩ s

/-- The fibre morphism of a proper morphism over a common base is proper. -/
instance instIsProper_pushforwardFiberMap {Y : Scheme.{u}} (f : X ⟶ S)
    (pY : Y ⟶ S) (h : X ⟶ Y) [IsProper h] (hc : h ≫ pY = f) (s : S) :
    IsProper (pushforwardFiberMap f pY h hc s) := by
  let q := pullback.map f (S.fromSpecResidueField s) pY (S.fromSpecResidueField s)
    h (𝟙 _) (𝟙 S) (by simpa using hc.symm) (by simp)
  have hq : IsProper q := by
    dsimp only [q]
    rw [pullback_map_eq_pullbackFstFstIso_inv]
    infer_instance
  have heq : pushforwardFiberMap f pY h hc s = q := by
    apply pullback.hom_ext
    · simp [pushforwardFiberMap, Scheme.Hom.fiberMap, q]
    · simp [pushforwardFiberMap, Scheme.Hom.fiberMap, q]
  exact heq.symm ▸ hq

/-- Proper pushforward of a family of fibrewise `r`-cycles along a morphism over `S`. -/
noncomputable def pushforward {Y : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {r : ℕ} (pY : Y ⟶ S) [LocallyOfFiniteType pY]
    (h : X ⟶ Y) [IsProper h] (hc : h ≫ pY = f) (α : f.FiberCycleFamily r) :
    pY.FiberCycleFamily r :=
  fun s ↦
    CycleGroup.mapHom (pushforwardFiberMap f pY h hc s)
      (f.fiberDimensionFunction s) (pY.fiberDimensionFunction s) r (α s)

/-- Coefficients of a proper pushforward are computed by `AlgebraicCycle.map`. -/
theorem pushforward_apply {Y : Scheme.{u}} {f : X ⟶ S}
    [LocallyOfFiniteType f] {r : ℕ} (pY : Y ⟶ S) [LocallyOfFiniteType pY]
    (h : X ⟶ Y) [IsProper h] (hc : h ≫ pY = f) (α : f.FiberCycleFamily r)
    (s : S) (y : pY.fiber s) :
    CycleGroup.toAlgebraicCycle (pY.fiberDimensionFunction s) r
        (pushforward pY h hc α s) y =
      AlgebraicCycle.map (pushforwardFiberMap f pY h hc s)
        (f.fiberDimensionFunction s) (pY.fiberDimensionFunction s)
        (CycleGroup.toAlgebraicCycle (f.fiberDimensionFunction s) r (α s)) y := rfl

end AlgebraicGeometry.RelativeCycle
