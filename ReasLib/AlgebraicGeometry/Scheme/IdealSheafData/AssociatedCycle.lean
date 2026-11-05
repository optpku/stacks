/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.CycleGroup
public import ReasLib.AlgebraicGeometry.Noetherian.IrreducibleComponents
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.GenericPointLength
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DeltaDimension

/-!
# Associated cycles of closed subschemes

This file defines the multiplicities of the irreducible components of a closed subscheme and
the cycle obtained by summing the components of a fixed dimension with those multiplicities.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- The multiplicity of a component of a closed subscheme is the length of its stalk as a
module over the ambient stalk. -/
noncomputable def componentMultiplicity [IsLocallyNoetherian X] (Z : X.IdealSheafData)
    (ξ : genericPoints Z.subscheme) : ℕ :=
  (Module.length (X.presheaf.stalk (Z.subschemeι ξ.1))
    ((ModuleCat.restrictScalars (Z.subschemeι.stalkMap ξ.1).hom).obj
      (ModuleCat.of (Z.subscheme.presheaf.stalk ξ.1)
        (Z.subscheme.presheaf.stalk ξ.1)))).toNat

/-- The natural-valued component multiplicity coerces to the corresponding ambient-stalk
module length. -/
theorem componentMultiplicity_eq_length [IsLocallyNoetherian X] (Z : X.IdealSheafData)
    (ξ : genericPoints Z.subscheme) :
    (componentMultiplicity Z ξ : ℕ∞) =
      Module.length (X.presheaf.stalk (Z.subschemeι ξ.1))
        ((ModuleCat.restrictScalars (Z.subschemeι.stalkMap ξ.1).hom).obj
          (ModuleCat.of (Z.subscheme.presheaf.stalk ξ.1)
            (Z.subscheme.presheaf.stalk ξ.1))) := sorry

/-- A reduced closed subscheme has multiplicity one at each of its generic points. -/
theorem componentMultiplicity_eq_one_of_isReduced [IsLocallyNoetherian X]
    (Z : X.IdealSheafData) [IsReduced Z.subscheme]
    (ξ : genericPoints Z.subscheme) : componentMultiplicity Z ξ = 1 := by
  let K := Z.subscheme.presheaf.stalk ξ.1
  let R := X.presheaf.stalk (Z.subschemeι ξ.1)
  let φ : R →+* K := (Z.subschemeι.stalkMap ξ.1).hom
  let M := (ModuleCat.restrictScalars φ).obj (ModuleCat.of K K)
  have hf : IsField K :=
    isField_stalk_of_closure_mem_irreducibleComponents Z.subscheme ξ.1 ξ.2
  letI := hf.toField
  letI : RingHomSurjective φ := ⟨Z.subschemeι.stalkMap_surjective ξ.1⟩
  let l : M →ₛₗ[φ] K :=
    { toFun := id
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  haveI : IsSimpleModule R M :=
    (l.isSimpleModule_iff_of_bijective Function.bijective_id).mpr inferInstance
  change (Module.length R M).toNat = 1
  rw [Module.length_eq_one]
  rfl

/-- The singleton algebraic cycle of a component, weighted by its multiplicity in the closed
subscheme. -/
noncomputable def componentCycle [IsLocallyNoetherian X] (Z : X.IdealSheafData)
    (ξ : genericPoints Z.subscheme) : AlgebraicCycle X ℤ :=
  @Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _
    (Z.subschemeι ξ.1) (componentMultiplicity Z ξ : ℤ)

/-- The component cycle is supported at its ambient generic point and has the component
multiplicity there. -/
theorem componentCycle_apply [IsLocallyNoetherian X] (Z : X.IdealSheafData)
    (ξ : genericPoints Z.subscheme) (x : X) :
    componentCycle Z ξ x =
      @ite ℤ (x = Z.subschemeι ξ.1) (Classical.propDecidable _)
        (componentMultiplicity Z ξ : ℤ) 0 := by
  classical
  simp only [componentCycle, Function.locallyFinsuppWithin.single_apply]

/-- The pointwise sum of the dimension-`k` component cycles has locally finite support. -/
theorem associatedCycleLocallyFiniteSupport [IsLocallyNoetherian X] (Z : X.IdealSheafData)
    (d : X → ℤ) (k : ℤ) :
    LocallyFiniteSupport (fun x : X ↦
      ∑ᶠ ξ : genericPoints Z.subscheme,
        @ite ℤ (d (Z.subschemeι ξ.1) = k) (Classical.propDecidable _)
          (componentCycle Z ξ x) 0) := sorry

/-- The underlying associated cycle is supported in dimension `k`. -/
theorem associatedCycle_mem_dimensionSubgroup [IsLocallyNoetherian X] (Z : X.IdealSheafData)
    (d : X → ℤ) (k : ℤ) :
    ({ toFun := fun x ↦ ∑ᶠ ξ : genericPoints Z.subscheme,
          @ite ℤ (d (Z.subschemeι ξ.1) = k) (Classical.propDecidable _)
            (componentCycle Z ξ x) 0
       supportWithinDomain' := Set.subset_univ _
       supportLocallyFiniteWithinDomain' :=
         fun x _ ↦ associatedCycleLocallyFiniteSupport Z d k x } :
      AlgebraicCycle X ℤ) ∈ AlgebraicCycle.dimensionSubgroup d k := sorry

/-- The multiplicity-weighted degree-`k` cycle associated to a closed subscheme. -/
noncomputable def associatedCycle [IsLocallyNoetherian X] (Z : X.IdealSheafData)
    (d : X → ℤ) (k : ℤ) : AlgebraicGeometry.CycleGroup X d k :=
  ⟨{ toFun := fun x ↦ ∑ᶠ ξ : genericPoints Z.subscheme,
        @ite ℤ (d (Z.subschemeι ξ.1) = k) (Classical.propDecidable _)
          (componentCycle Z ξ x) 0
     supportWithinDomain' := Set.subset_univ _
     supportLocallyFiniteWithinDomain' :=
       fun x _ ↦ associatedCycleLocallyFiniteSupport Z d k x },
    associatedCycle_mem_dimensionSubgroup Z d k⟩

/-- Coefficients of the associated cycle are the pointwise finite sum of the multiplicity-weighted
dimension-`k` component cycles. -/
theorem associatedCycle_apply [IsLocallyNoetherian X] (Z : X.IdealSheafData)
    (d : X → ℤ) (k : ℤ) (x : X) :
    (associatedCycle Z d k : AlgebraicCycle X ℤ) x =
      ∑ᶠ ξ : genericPoints Z.subscheme,
        @ite ℤ (d (Z.subschemeι ξ.1) = k) (Classical.propDecidable _)
          (componentCycle Z ξ x) 0 := rfl

/-- The associated cycle of a reduced point closure has coefficient one at
that point (in the prescribed dimension) and zero elsewhere. -/
theorem associatedCycle_pointClosure_apply [IsLocallyNoetherian X]
    (x : X) (d : X → ℤ) (k : ℤ) (y : X) :
    ((Scheme.PointClosure.reducedStructure x).ideal.associatedCycle d k).1 y =
      @ite ℤ (y = x ∧ d x = k) (Classical.propDecidable _) 1 0 := by
  classical
  let Z := (Scheme.PointClosure.reducedStructure x).ideal
  haveI : IsReduced Z.subscheme :=
    inferInstanceAs (IsReduced (vanishingIdeal (Scheme.PointClosure.closedSubset x)).subscheme)
  have hrange : Set.range Z.subschemeι = closure {x} :=
    Scheme.PointClosure.range_ι x
  obtain ⟨z, hz⟩ : ∃ z, Z.subschemeι z = x := by
    rw [← Set.mem_range, hrange]
    exact subset_closure (Set.mem_singleton x)
  have hc : closure {z} = (Set.univ : Set Z.subscheme) := by
    rw [Z.subschemeι.isEmbedding.closure_eq_preimage_closure_image, Set.image_singleton, hz]
    ext w
    simp only [Set.mem_preimage, Set.mem_univ, iff_true]
    rw [← hrange]
    exact ⟨w, rfl⟩
  haveI : IrreducibleSpace Z.subscheme :=
    (irreducibleSpace_def _).mpr (by
      change IsIrreducible (Set.univ : Set Z.subscheme)
      rw [← hc]
      exact isIrreducible_singleton.closure)
  have hgeneric : genericPoints Z.subscheme = {z} := by
    rw [genericPoints_eq_singleton]
    congr 1
    exact (genericPoint_spec Z.subscheme).eq hc
  let ξ : genericPoints Z.subscheme := ⟨z, by rw [hgeneric]; exact Set.mem_singleton z⟩
  have hall : ∀ η : genericPoints Z.subscheme, η = ξ := by
    intro η
    apply Subtype.ext
    have h := η.2
    simpa only [hgeneric, Set.mem_singleton_iff] using h
  rw [associatedCycle_apply]
  rw [finsum_eq_single _ ξ (fun η hη ↦ (hη (hall η)).elim)]
  rw [componentCycle_apply, componentMultiplicity_eq_one_of_isReduced]
  simp only [show (Scheme.PointClosure.reducedStructure x).ideal.subschemeι ξ.1 = x from hz]
  split_ifs <;> simp_all

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.Hom

/-- The degree-`k` cycle of a closed subscheme, measured using the relative dimension function
of a locally finite type morphism. -/
noncomputable def closedSubschemeCycle
    {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (Z : X.IdealSheafData) (k : ℤ)
    (hZ : f.closedSubschemeDeltaDimension δ Z ≤ (k : EInt)) :
    AlgebraicGeometry.CycleGroup X (f.relativeDimensionFunction δ) k :=
  @IdealSheafData.associatedCycle X (LocallyOfFiniteType.isLocallyNoetherian f) Z
    (f.relativeDimensionFunction δ) k

/-- Coefficients of the closed-subscheme cycle are the multiplicity-weighted sum over its
dimension-`k` generic points. -/
theorem closedSubschemeCycle_apply
    {X S : Scheme.{u}} (f : X ⟶ S) [UniversallyCatenary S] [LocallyOfFiniteType f]
    (δ : S → ℤ) [IsDimensionFunction δ] (Z : X.IdealSheafData) (k : ℤ)
    (hZ : f.closedSubschemeDeltaDimension δ Z ≤ (k : EInt)) (x : X) :
    (closedSubschemeCycle f δ Z k hZ : AlgebraicCycle X ℤ) x =
      ∑ᶠ ξ : genericPoints Z.subscheme,
        @ite ℤ (f.relativeDimensionFunction δ (Z.subschemeι ξ.1) = k)
          (Classical.propDecidable _)
          (@IdealSheafData.componentCycle X
            (LocallyOfFiniteType.isLocallyNoetherian f) Z ξ x) 0 := rfl

end AlgebraicGeometry.Scheme.Hom
