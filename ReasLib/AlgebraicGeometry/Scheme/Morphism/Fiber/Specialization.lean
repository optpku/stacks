/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import ReasLib.AlgebraicGeometry.CycleGroup
public import ReasLib.AlgebraicGeometry.CycleGroup.Point
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedCycle
public import ReasLib.AlgebraicGeometry.Scheme.Module.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Module.FiberSupportDimension
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Coherent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.ResidueField
public import ReasLib.RingTheory.Catenary.DimensionOne
public import ReasLib.RingTheory.Catenary.Field

/-!
# Specialization of cycles over a discrete valuation ring

This file constructs the specialization map on cycles of a scheme locally of
finite type over a discrete valuation ring.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry

/-- A discrete valuation ring is universally catenary. -/
instance instUniversallyCatenaryRing_of_isDiscreteValuationRing
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    UniversallyCatenaryRing.{u, u} R :=
  UniversallyCatenaryRing.of_isDomain_ringKrullDim_eq_one
    (IsDiscreteValuationRing.ringKrullDim_eq_one R)

/-- A scheme locally of finite type over a discrete valuation ring is locally Noetherian. -/
theorem isLocallyNoetherian_of_locallyOfFiniteType_dvr
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f] :
    IsLocallyNoetherian X :=
  LocallyOfFiniteType.isLocallyNoetherian f

namespace Scheme.Hom

/-- Scheme-theoretic fibres of a locally finite type morphism are locally Noetherian. -/
instance instIsLocallyNoetherian_fiber {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (s : S) :
    IsLocallyNoetherian (f.fiber s) := by
  exact @LocallyOfFiniteType.isLocallyNoetherian
    (Limits.pullback f (S.fromSpecResidueField s)) (Spec (S.residueField s))
    (Limits.pullback.snd f (S.fromSpecResidueField s))
    (MorphismProperty.pullback_snd _ _ inferInstance)
    (isLocallyNoetherian_Spec.mpr inferInstance)

/-- The standard dimension function on a scheme-theoretic fibre, obtained by viewing the
fibre as a scheme locally of finite type over the residue field of the base point. -/
noncomputable abbrev fiberDimensionFunction {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (s : S) :
    f.fiber s → ℤ :=
  @Scheme.Hom.relativeDimensionFunction _ _ (f.fiberToSpecResidueField s)
    (inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField s)))) (fun _ ↦ 0)

/-- The fibre dimension function is the relative dimension function of
`fiberToSpecResidueField` against the zero function on the residue field. -/
theorem fiberDimensionFunction_apply {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (s : S)
    (x : f.fiber s) :
    f.fiberDimensionFunction s x =
      @Scheme.Hom.relativeDimensionFunction _ _ (f.fiberToSpecResidueField s)
    (inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField s)))) (fun _ ↦ 0) x := rfl

/-- The fibre dimension function is a dimension function. -/
instance instIsDimensionFunction_fiberDimensionFunction {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] (s : S) :
    IsDimensionFunction (f.fiberDimensionFunction s) := by
  letI : LocallyOfFiniteType (f.fiberToSpecResidueField s) :=
    inferInstanceAs (LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField s)))
  exact instIsDimensionFunctionRelativeDimensionFunction
    (f.fiberToSpecResidueField s) (fun _ ↦ 0)

/-- The generic fibre `X_K` of a morphism to the spectrum of a domain. -/
noncomputable abbrev genericFiber {R : Type u} [CommRing R] [IsDomain R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) : Scheme.{u} :=
  f.fiber (genericPoint (Spec (CommRingCat.of R)))

/-- The closed fibre `X_κ` of a morphism to the spectrum of a local ring. -/
noncomputable abbrev specialFiber {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) : Scheme.{u} :=
  f.fiber (IsLocalRing.closedPoint R)

/-- The canonical immersion of the generic fibre into `X`. -/
noncomputable abbrev genericFiberι {R : Type u} [CommRing R] [IsDomain R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    f.genericFiber ⟶ X :=
  f.fiberι (genericPoint (Spec (CommRingCat.of R)))

/-- The canonical immersion of the special fibre into `X`. -/
noncomputable abbrev specialFiberι {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    f.specialFiber ⟶ X :=
  f.fiberι (IsLocalRing.closedPoint R)

/-- The generic fibre is the fibre over the generic point. -/
theorem genericFiber_fiber {R : Type u} [CommRing R] [IsDomain R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    f.genericFiber = f.fiber (genericPoint (Spec (CommRingCat.of R))) := rfl

/-- The special fibre is the fibre over the closed point. -/
theorem specialFiber_fiber {R : Type u} [CommRing R] [IsLocalRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) :
    f.specialFiber = f.fiber (IsLocalRing.closedPoint R) := rfl

/-- The scheme-theoretic image in `X` of the reduced closure of a point of the generic
fibre. -/
noncomputable def pointImage {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (z : f.genericFiber) : X.IdealSheafData :=
  (PointClosure.ι z ≫ f.genericFiberι).ker

/-- The closed subscheme of the special fibre obtained by pulling back the scheme-theoretic
image of a generic-fibre point. -/
noncomputable def pointImageSpecial {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (z : f.genericFiber) :
    f.specialFiber.IdealSheafData :=
  (f.pointImage z).comap f.specialFiberι

private theorem fiberι_quasiCompact_of_isAffine {X S : Scheme.{u}} [IsAffine S]
    (f : X ⟶ S) (s : S) : QuasiCompact (f.fiberι s) :=
  inferInstanceAs (QuasiCompact (Limits.pullback.fst f (S.fromSpecResidueField s)))

/-- The scheme-theoretic image of the reduced closure of a generic-fibre point is the
closure of its image in `X`. -/
theorem pointImage_spec {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (z : f.genericFiber) :
    ((f.pointImage z).support : Set X) =
      closure (Set.range (PointClosure.ι z ≫ f.genericFiberι)) := by
  letI := fiberι_quasiCompact_of_isAffine f
    (genericPoint (Spec (CommRingCat.of R)))
  simpa only [pointImage] using
    (Scheme.Hom.support_ker (PointClosure.ι z ≫ f.genericFiberι))

/-- The support of the special-fibre pullback of a point image is the preimage of the
ambient scheme-theoretic image. -/
theorem support_pointImageSpecial {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (z : f.genericFiber) :
    ((f.pointImageSpecial z).support : Set (f.specialFiber)) =
      (f.pointImage z).support.preimage f.specialFiberι.continuous := by
  exact congrArg (fun Z : Closeds f.specialFiber ↦ (Z : Set f.specialFiber))
    (IdealSheafData.support_comap (f.pointImage z) f.specialFiberι)

private theorem associatedCycle_support_subset {Y : Scheme.{u}} [IsLocallyNoetherian Y]
    (Z : Y.IdealSheafData) (d : Y → ℤ) (r : ℤ) :
    (CycleGroup.toAlgebraicCycle d r (Z.associatedCycle d r)).support ⊆ Z.support := by
  classical
  intro x hx
  by_contra hxZ
  apply hx
  change (∑ᶠ ξ : genericPoints Z.subscheme,
    @ite ℤ (d (Z.subschemeι ξ.1) = r) (Classical.propDecidable _)
      (Z.componentCycle ξ x) 0) = 0
  have hterm (ξ : genericPoints Z.subscheme) :
      @ite ℤ (d (Z.subschemeι ξ.1) = r) (Classical.propDecidable _)
        (Z.componentCycle ξ x) 0 = 0 := by
    have hne : x ≠ Z.subschemeι ξ.1 := by
      intro heq
      apply hxZ
      rw [heq, ← Z.range_subschemeι]
      exact ⟨ξ.1, rfl⟩
    simp [IdealSheafData.componentCycle, hne]
  simp only [hterm, finsum_zero]

private theorem genericFiber_mem_open_of_pointImageSpecial
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    (z : f.genericFiber) (U : X.Opens) {x : f.specialFiber}
    (hx : x ∈ (f.pointImageSpecial z).support) (hU : f.specialFiberι x ∈ U) :
    f.genericFiberι z ∈ U := by
  have hx' : f.specialFiberι x ∈
      closure (Set.range (PointClosure.ι z ≫ f.genericFiberι)) := by
    change x ∈ ((f.pointImageSpecial z).support : Set f.specialFiber) at hx
    rw [support_pointImageSpecial] at hx
    change f.specialFiberι x ∈ ((f.pointImage z).support : Set X) at hx
    rwa [pointImage_spec] at hx
  obtain ⟨_, hyU, y, rfl⟩ := mem_closure_iff.mp hx' U U.isOpen hU
  have hy : PointClosure.ι z y ∈ closure ({z} : Set f.genericFiber) := by
    have hr : Set.range (PointClosure.ι z) = closure ({z} : Set f.genericFiber) :=
      IdealSheafData.range_vanishingIdeal_subschemeι (PointClosure.closedSubset z)
    rw [← hr]
    exact ⟨y, rfl⟩
  have hopen : IsOpen (f.genericFiberι ⁻¹' (U : Set X)) :=
    U.isOpen.preimage f.genericFiberι.continuous
  obtain ⟨w, hwU, hwz⟩ := mem_closure_iff.mp hy _ hopen hyU
  have hw : w = z := hwz
  rw [← hw]
  exact hwU

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [LocallyOfFiniteType f]

/-- The coefficient of a specialized cycle at a special-fibre point. -/
noncomputable def cycleSpecializationCoeff (r : ℕ)
    (α : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r)
    (x : f.specialFiber) : ℤ :=
  ∑ᶠ z : f.genericFiber,
    CycleGroup.toAlgebraicCycle
        (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r α z *
      (CycleGroup.toAlgebraicCycle
          (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r
          (IdealSheafData.associatedCycle (f.pointImageSpecial z)
            (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r)) x

private theorem specialization_finite_contributors (r : ℕ)
    (α : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r)
    (U : X.Opens) (hU : IsCompact (U : Set X)) :
    {z : f.genericFiber | ∃ x : f.specialFiber, f.specialFiberι x ∈ U ∧
      CycleGroup.toAlgebraicCycle
        (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r α z *
      CycleGroup.toAlgebraicCycle
        (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r
        (IdealSheafData.associatedCycle (f.pointImageSpecial z)
          (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r) x ≠ 0}.Finite := by
  letI := fiberι_quasiCompact_of_isAffine f
    (genericPoint (Spec (CommRingCat.of R)))
  have hfin := (CycleGroup.toAlgebraicCycle _ _ α).locallyFiniteSupport
    |>.finite_inter_support_of_isCompact (f.genericFiberι.isCompact_preimage hU)
  refine hfin.subset ?_
  rintro z ⟨x, hxU, hz⟩
  have ha : CycleGroup.toAlgebraicCycle
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r α z ≠ 0 :=
    left_ne_zero_of_mul hz
  have hc : CycleGroup.toAlgebraicCycle
      (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r
      (IdealSheafData.associatedCycle (f.pointImageSpecial z)
        (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r) x ≠ 0 :=
    right_ne_zero_of_mul hz
  exact ⟨genericFiber_mem_open_of_pointImageSpecial f z U
    (associatedCycle_support_subset _ _ _ hc) hxU, ha⟩

private theorem specialization_finite_support (r : ℕ)
    (α : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r)
    (x : f.specialFiber) :
    Function.HasFiniteSupport (fun z : f.genericFiber ↦
      CycleGroup.toAlgebraicCycle
        (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r α z *
      CycleGroup.toAlgebraicCycle
        (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r
        (IdealSheafData.associatedCycle (f.pointImageSpecial z)
          (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r) x) := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f.specialFiberι x)) isOpen_univ
  exact (specialization_finite_contributors f r α U hU.isCompact).subset
    (fun z hz ↦ ⟨x, hxU, hz⟩)

/-- The coefficient function of specialization has locally finite support. -/
theorem cycleSpecializationLocallyFiniteSupport (r : ℕ)
    (α : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r) :
    LocallyFiniteSupport (cycleSpecializationCoeff f r α) := by
  classical
  intro x
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f.specialFiberι x)) isOpen_univ
  let a := CycleGroup.toAlgebraicCycle
    (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r α
  let c (z : f.genericFiber) := CycleGroup.toAlgebraicCycle
    (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r
    (IdealSheafData.associatedCycle (f.pointImageSpecial z)
      (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r)
  let V := f.specialFiberι ⁻¹' (U : Set X)
  let T := {z : f.genericFiber | ∃ y ∈ V, a z * c z y ≠ 0}
  have hT : T.Finite := specialization_finite_contributors f r α U hU.isCompact
  letI := fiberι_quasiCompact_of_isAffine f (IsLocalRing.closedPoint R)
  have hV : IsCompact V := f.specialFiberι.isCompact_preimage hU.isCompact
  have hc (z : f.genericFiber) : (V ∩ (c z).support).Finite :=
    (c z).locallyFiniteSupport.finite_inter_support_of_isCompact hV
  refine ⟨V, (U.isOpen.preimage f.specialFiberι.continuous).mem_nhds hxU, ?_⟩
  refine (hT.biUnion (fun z _ ↦ hc z)).subset ?_
  rintro y ⟨hyV, hy⟩
  have hterm : ∃ z, a z * c z y ≠ 0 := by
    by_contra! hzero
    apply hy
    change (∑ᶠ z, a z * c z y) = 0
    simp only [hzero, finsum_zero]
  obtain ⟨z, hz⟩ := hterm
  exact Set.mem_iUnion₂.mpr ⟨z, ⟨y, hyV, hz⟩, hyV, right_ne_zero_of_mul hz⟩

/-- The underlying algebraic cycle of specialization. -/
noncomputable def cycleSpecializationCycle (r : ℕ)
    (α : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r) :
    AlgebraicCycle f.specialFiber ℤ where
  toFun := cycleSpecializationCoeff f r α
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' := fun x _ ↦
    cycleSpecializationLocallyFiniteSupport f r α x

/-- The underlying specialization cycle is supported in dimension `r`. -/
theorem cycleSpecializationCycle_mem_dimensionSubgroup (r : ℕ)
    (α : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r) :
    cycleSpecializationCycle f r α ∈
      AlgebraicCycle.dimensionSubgroup
        (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r := by
  rw [AlgebraicCycle.mem_dimensionSubgroup]
  intro x hx
  by_contra hdim
  apply hx
  change cycleSpecializationCoeff f r α x = 0
  unfold cycleSpecializationCoeff
  trans ∑ᶠ _ : f.genericFiber, (0 : ℤ)
  · apply finsum_congr
    intro z
    have hxz :
        CycleGroup.toAlgebraicCycle
          (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r
          (IdealSheafData.associatedCycle (f.pointImageSpecial z)
            (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r) x = 0 := by
      exact CycleGroup.apply_eq_zero_of_dimension_ne _ _ _ hdim
    rw [hxz, mul_zero]
  · simp

/-- The underlying degree-`r` cycle of specialization. -/
noncomputable def cycleSpecializationValue (r : ℕ)
    (α : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r) :
    CycleGroup f.specialFiber
      (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r :=
  ⟨cycleSpecializationCycle f r α,
    cycleSpecializationCycle_mem_dimensionSubgroup f r α⟩

/-- Specialization sends the zero cycle to zero. -/
theorem cycleSpecializationValue_zero (r : ℕ) :
    cycleSpecializationValue f r 0 = 0 := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  change cycleSpecializationCoeff f r 0 x = 0
  simp [cycleSpecializationCoeff]

/-- Specialization preserves addition of degree-`r` cycles. -/
theorem cycleSpecializationValue_add (r : ℕ)
    (a b : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r) :
    cycleSpecializationValue f r (a + b) =
      cycleSpecializationValue f r a + cycleSpecializationValue f r b := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  change cycleSpecializationCoeff f r (a + b) x =
    cycleSpecializationCoeff f r a x + cycleSpecializationCoeff f r b x
  simp only [cycleSpecializationCoeff, map_add,
    Function.locallyFinsuppWithin.coe_add, Pi.add_apply, add_mul]
  exact finsum_add_distrib (specialization_finite_support f r a x)
    (specialization_finite_support f r b x)

/-- The specialization map `sp_{X/R}` on degree-`r` cycles of the generic fibre. -/
noncomputable def cycleSpecialization (r : ℕ) :
    CycleGroup f.genericFiber
        (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r →+
      CycleGroup f.specialFiber
        (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r where
  toFun := cycleSpecializationValue f r
  map_zero' := cycleSpecializationValue_zero f r
  map_add' := cycleSpecializationValue_add f r

/-- Coefficients of specialization are the locally finite sum of input coefficients times
the associated cycles of special-fibre point images. -/
theorem cycleSpecialization_apply (r : ℕ)
    (α : CycleGroup f.genericFiber
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r)
    (x : f.specialFiber) :
    CycleGroup.toAlgebraicCycle
        (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r
        (f.cycleSpecialization r α) x =
      cycleSpecializationCoeff f r α x := rfl

/-- On the cycle of an integral closed subscheme of the generic fibre, specialization is
the degree-`r` associated cycle of the special fibre of its scheme-theoretic image. -/
theorem cycleSpecialization_point (r : ℕ) (z : f.genericFiber)
    (hz : f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R))) z = r) :
    CycleGroup.toAlgebraicCycle
        (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r
        (f.cycleSpecialization r
          (CycleGroup.point
            (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r z hz)) =
      CycleGroup.toAlgebraicCycle
        (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r
        (IdealSheafData.associatedCycle (f.pointImageSpecial z)
          (f.fiberDimensionFunction (IsLocalRing.closedPoint R)) r) := by
  classical
  apply Function.locallyFinsuppWithin.ext
  intro x
  change cycleSpecializationCoeff f r
    (CycleGroup.point
      (f.fiberDimensionFunction (genericPoint (Spec (CommRingCat.of R)))) r z hz) x = _
  unfold cycleSpecializationCoeff
  rw [finsum_eq_single _ z]
  · simp [CycleGroup.toAlgebraicCycle, CycleGroup.point]
  · intro y hy
    simp [CycleGroup.toAlgebraicCycle, CycleGroup.point, hy]

end Scheme.Hom

end AlgebraicGeometry
