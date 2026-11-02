/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.ChowGroup.WeilDivisor
public import ReasLib.AlgebraicGeometry.CycleGroup.FlatPullback.Principal
public import ReasLib.AlgebraicGeometry.CycleGroup.Reindex
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.MeromorphicSection.Pullback

/-!
# Flat pullback of divisors by irreducible components

This file constructs the multiplicity-weighted sum of divisor cycles obtained by pulling a
meromorphic section back to the reduced irreducible components of the source of a flat morphism.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.CycleGroup

open Scheme.Modules.MeromorphicSection

/-- The two natural expressions for the degree of a flat component divisor agree. -/
theorem flatDivisorDegree (n : ℤ) (r : ℕ) :
    (n - 1) + (r : ℤ) = n + (r : ℤ) - 1 := by
  simpa only [sub_eq_add_neg] using add_right_comm n (-1) (r : ℤ)

private theorem flatDivisor_relativeDimension_comp
    {X Y S : Scheme.{u}} (i : X ⟶ Y) [SurjectiveOnStalks i]
    (p : Y ⟶ S) [LocallyOfFiniteType p] [LocallyOfFiniteType (i ≫ p)]
    (δ : S → ℤ) (x : X) :
    (i ≫ p).relativeDimensionFunction δ x = p.relativeDimensionFunction δ (i x) := by
  have hsurj : Function.Surjective (i.residueFieldMap x).hom := by
    intro a
    obtain ⟨b, rfl⟩ := X.residue_surjective x a
    obtain ⟨c, hc⟩ := i.stalkMap_surjective x b
    refine ⟨Y.residue (i x) c, ?_⟩
    have h := ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i x) c
    simpa only [CommRingCat.comp_apply, hc] using h
  letI : Algebra (S.residueField (p (i x))) (Y.residueField (i x)) :=
    Scheme.Hom.residueFieldAlgebra p (i x)
  letI : Algebra (S.residueField (p (i x))) (X.residueField x) :=
    Scheme.Hom.residueFieldAlgebra (i ≫ p) x
  let e : Y.residueField (i x) ≃ₐ[S.residueField (p (i x))] X.residueField x :=
    AlgEquiv.ofRingEquiv
      (f := RingEquiv.ofBijective (i.residueFieldMap x).hom ⟨RingHom.injective _, hsurj⟩)
      (fun a ↦ by
        change (i.residueFieldMap x).hom ((p.residueFieldMap (i x)).hom a) =
          ((i ≫ p).residueFieldMap x).hom a
        rw [Scheme.residueFieldMap_comp]
        rfl)
  have ht := e.trdeg_eq
  exact congrArg (fun k ↦ δ (p (i x)) + ((Cardinal.toENat k).toNat : ℤ)) ht.symm

/-- The divisor of a section pulled back to a reduced irreducible component has degree
`(n - 1) + r`. -/
theorem flatComponentDivisorCycle_mem
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral Y.left] (n : ℤ)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = n)
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (ℒ : Y.left.Modules) [Scheme.Modules.Invertible ℒ]
    (s : Y.left.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0)
    (C : irreducibleComponents X.left) :
    @Scheme.nonzeroMeromorphicSectionDivisorCycle
        (Scheme.PointClosure.scheme (genericPoints.ofComponent C).1)
        (@Scheme.PointClosure.scheme_isLocallyNoetherian X.left
          (LocallyOfFiniteType.isLocallyNoetherian X.hom)
          (genericPoints.ofComponent C).1)
        inferInstance
        ((Scheme.Modules.pullback
          (Scheme.PointClosure.ι (genericPoints.ofComponent C).1 ≫ f.left)).obj ℒ)
        (Scheme.Modules.Invertible.pullback
          (Scheme.PointClosure.ι (genericPoints.ofComponent C).1 ≫ f.left) inferInstance)
        (pullbackToFlatComponent f.left ℒ s C)
        (pullbackToFlatComponent_ne_zero f.left ℒ s hs C) ∈
      AlgebraicCycle.dimensionSubgroup
        ((Scheme.PointClosure.ι (genericPoints.ofComponent C).1 ≫ X.hom).relativeDimensionFunction δ)
        ((n - 1) + (r : ℤ)) := by
  apply relativeDivisorCycle_mem
    (Scheme.PointClosure.ι (genericPoints.ofComponent C).1 ≫ X.hom) δ
  rw [flatDivisor_relativeDimension_comp]
  have hgeneric :
      (Scheme.PointClosure.ι (genericPoints.ofComponent C).1)
          (genericPoint (Scheme.PointClosure.scheme (genericPoints.ofComponent C).1)) =
        (genericPoints.ofComponent C).1 := by
    have h :=
      (genericPoint_spec (Scheme.PointClosure.scheme (genericPoints.ofComponent C).1)).image
        (Scheme.PointClosure.ι (genericPoints.ofComponent C).1).continuous
    have hrange : Set.range (Scheme.PointClosure.ι (genericPoints.ofComponent C).1) =
        closure ({(genericPoints.ofComponent C).1} : Set X.left) :=
      Scheme.IdealSheafData.range_vanishingIdeal_subschemeι _
    rw [Set.image_univ, hrange, closure_closure] at h
    exact h.eq isGenericPoint_closure
  rw [hgeneric]
  exact Scheme.Hom.flatComponent_dimension δ X Y n hY f r (genericPoints.ofComponent C)

/-- The divisor cycle of a section pulled back to a reduced irreducible component, pushed
forward to the source and expressed in degree `n + r - 1`. -/
noncomputable def flatComponentDivisorCycle
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral Y.left] (n : ℤ)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = n)
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (ℒ : Y.left.Modules) [Scheme.Modules.Invertible ℒ]
    (s : Y.left.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0)
    (C : irreducibleComponents X.left) :
    CycleGroup X.left (X.hom.relativeDimensionFunction δ) (n + (r : ℤ) - 1) :=
  reindex (X.hom.relativeDimensionFunction δ) (flatDivisorDegree n r)
    (mapHom (Scheme.PointClosure.ι (genericPoints.ofComponent C).1)
      ((Scheme.PointClosure.ι (genericPoints.ofComponent C).1 ≫ X.hom).relativeDimensionFunction δ)
      (X.hom.relativeDimensionFunction δ) ((n - 1) + (r : ℤ))
      ⟨@Scheme.nonzeroMeromorphicSectionDivisorCycle
          (Scheme.PointClosure.scheme (genericPoints.ofComponent C).1)
          (@Scheme.PointClosure.scheme_isLocallyNoetherian X.left
            (LocallyOfFiniteType.isLocallyNoetherian X.hom)
            (genericPoints.ofComponent C).1)
          inferInstance
          ((Scheme.Modules.pullback
            (Scheme.PointClosure.ι (genericPoints.ofComponent C).1 ≫ f.left)).obj ℒ)
          (Scheme.Modules.Invertible.pullback
            (Scheme.PointClosure.ι (genericPoints.ofComponent C).1 ≫ f.left) inferInstance)
          (pullbackToFlatComponent f.left ℒ s C)
          (pullbackToFlatComponent_ne_zero f.left ℒ s hs C),
        flatComponentDivisorCycle_mem δ X Y n hY f r ℒ s hs C⟩)

/-- Forgetting the degree of a component divisor cycle gives the pushforward of its divisor on
the reduced component closure. -/
theorem flatComponentDivisorCycle_toAlgebraicCycle
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral Y.left] (n : ℤ)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = n)
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (ℒ : Y.left.Modules) [Scheme.Modules.Invertible ℒ]
    (s : Y.left.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0)
    (C : irreducibleComponents X.left) :
    toAlgebraicCycle (X.hom.relativeDimensionFunction δ) (n + (r : ℤ) - 1)
        (flatComponentDivisorCycle δ X Y n hY f r ℒ s hs C) =
      AlgebraicCycle.map (Scheme.PointClosure.ι (genericPoints.ofComponent C).1)
        ((Scheme.PointClosure.ι (genericPoints.ofComponent C).1 ≫ X.hom).relativeDimensionFunction δ)
        (X.hom.relativeDimensionFunction δ)
        (@Scheme.nonzeroMeromorphicSectionDivisorCycle
          (Scheme.PointClosure.scheme (genericPoints.ofComponent C).1)
          (@Scheme.PointClosure.scheme_isLocallyNoetherian X.left
            (LocallyOfFiniteType.isLocallyNoetherian X.hom)
            (genericPoints.ofComponent C).1)
          inferInstance
          ((Scheme.Modules.pullback
            (Scheme.PointClosure.ι (genericPoints.ofComponent C).1 ≫ f.left)).obj ℒ)
          (Scheme.Modules.Invertible.pullback
            (Scheme.PointClosure.ι (genericPoints.ofComponent C).1 ≫ f.left) inferInstance)
          (pullbackToFlatComponent f.left ℒ s C)
          (pullbackToFlatComponent_ne_zero f.left ℒ s hs C)) := by
  have hreindex {a b : ℤ} (h : a = b)
      (α : CycleGroup X.left (X.hom.relativeDimensionFunction δ) a) :
      toAlgebraicCycle (X.hom.relativeDimensionFunction δ) b
          (reindex (X.hom.relativeDimensionFunction δ) h α) =
        toAlgebraicCycle (X.hom.relativeDimensionFunction δ) a α := by
    cases h
    rfl
  exact (hreindex (flatDivisorDegree n r) _).trans rfl

private theorem flatDivisor_components_locallyFinite
    (X : Scheme.{u}) [IsLocallyNoetherian X] :
    LocallyFinite fun C : irreducibleComponents X ↦ (C : Set X) := by
  intro x
  obtain ⟨U, hU, hxU, _⟩ :=
    exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
  refine ⟨U, U.2.mem_nhds hxU, ?_⟩
  letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  letI : NoetherianSpace U := noetherianSpace_of_isAffineOpen U hU
  letI : Finite (irreducibleComponents U) := NoetherianSpace.finite_irreducibleComponents
  let J := {C : irreducibleComponents X // ((C : Set X) ∩ U).Nonempty}
  let componentMap : J → irreducibleComponents U := fun C ↦
    ⟨Subtype.val ⁻¹' (C.1 : Set X),
      preimage_mem_irreducibleComponents C.1.2 U.2.isOpenEmbedding_subtypeVal
        (by
          obtain ⟨y, hyC, hyU⟩ := C.2
          exact ⟨y, hyC, ⟨⟨y, hyU⟩, rfl⟩⟩)⟩
  have recover (C : J) :
      closure (Subtype.val '' (componentMap C : Set U)) = (C.1 : Set X) := by
    apply closure_image_preimage_of_isPreirreducible Subtype.val
      U.2.isOpenEmbedding_subtypeVal.isOpenMap (C.1 : Set X)
    · obtain ⟨y, hyC, hyU⟩ := C.2
      exact ⟨⟨y, hyU⟩, hyC⟩
    · exact C.1.2.1.2
    · exact isClosed_of_mem_irreducibleComponents _ C.1.2
  haveI : Finite J := Finite.of_injective componentMap fun C D h ↦ by
    apply Subtype.ext
    apply Subtype.ext
    rw [← recover C, h, recover D]
  exact (Set.finite_coe_iff).mp (show Finite J from inferInstance)

/-- The generic-multiplicity-weighted component divisor cycles form a locally finite family. -/
theorem flatComponentDivisorsLocallyFinite
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral Y.left] (n : ℤ)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = n)
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (ℒ : Y.left.Modules) [Scheme.Modules.Invertible ℒ]
    (s : Y.left.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0) :
    LocallyFinite fun C : irreducibleComponents X.left ↦
      (toAlgebraicCycle (X.hom.relativeDimensionFunction δ) (n + (r : ℤ) - 1)
        ((@AlgebraicCycle.genericMultiplicity X.left
            (LocallyOfFiniteType.isLocallyNoetherian X.hom)
            (genericPoints.ofComponent C) : ℤ) •
          flatComponentDivisorCycle δ X Y n hY f r ℒ s hs C)).support := by
  letI : IsLocallyNoetherian X.left := LocallyOfFiniteType.isLocallyNoetherian X.hom
  apply (flatDivisor_components_locallyFinite X.left).subset
  intro C x hx
  have hnonzero :
      toAlgebraicCycle (X.hom.relativeDimensionFunction δ) (n + (r : ℤ) - 1)
        (flatComponentDivisorCycle δ X Y n hY f r ℒ s hs C) x ≠ 0 := by
    intro hzero
    apply hx
    change (_ : ℤ) •
      (toAlgebraicCycle (X.hom.relativeDimensionFunction δ) (n + (r : ℤ) - 1)
        (flatComponentDivisorCycle δ X Y n hY f r ℒ s hs C) x) = 0
    rw [hzero, smul_zero]
  rw [flatComponentDivisorCycle_toAlgebraicCycle] at hnonzero
  change (∑ᶠ y ∈ (Scheme.PointClosure.ι (genericPoints.ofComponent C).1).base ⁻¹' {x},
    _ * (AlgebraicCycle.mapCoeff _ _ _ y : ℤ)) ≠ 0 at hnonzero
  obtain ⟨y, hy, _⟩ := exists_ne_zero_of_finsum_mem_ne_zero hnonzero
  have hxrange : x ∈ Set.range (Scheme.PointClosure.ι (genericPoints.ofComponent C).1) :=
    ⟨y, hy⟩
  have hrange : Set.range (Scheme.PointClosure.ι (genericPoints.ofComponent C).1) =
      closure ({(genericPoints.ofComponent C).1} : Set X.left) := by
    exact Scheme.IdealSheafData.range_vanishingIdeal_subschemeι _
  rw [hrange, genericPoints.isGenericPoint_ofComponent C] at hxrange
  exact hxrange

/-- The locally finite sum of component divisor cycles weighted by their generic
multiplicities. -/
noncomputable def flatComponentDivisorSum
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral Y.left] (n : ℤ)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = n)
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (ℒ : Y.left.Modules) [Scheme.Modules.Invertible ℒ]
    (s : Y.left.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0) :
    CycleGroup X.left (X.hom.relativeDimensionFunction δ) (n + (r : ℤ) - 1) :=
  locallyFiniteSum (X.hom.relativeDimensionFunction δ) (n + (r : ℤ) - 1)
    (fun C : irreducibleComponents X.left ↦
      (@AlgebraicCycle.genericMultiplicity X.left
        (LocallyOfFiniteType.isLocallyNoetherian X.hom)
        (genericPoints.ofComponent C) : ℤ) •
        flatComponentDivisorCycle δ X Y n hY f r ℒ s hs C)
    (flatComponentDivisorsLocallyFinite δ X Y n hY f r ℒ s hs)

/-- Evaluation of the component divisor sum is the corresponding pointwise finite sum. -/
theorem flatComponentDivisorSum_apply
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral Y.left] (n : ℤ)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = n)
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (ℒ : Y.left.Modules) [Scheme.Modules.Invertible ℒ]
    (s : Y.left.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0)
    (x : X.left) :
    toAlgebraicCycle (X.hom.relativeDimensionFunction δ) (n + (r : ℤ) - 1)
        (flatComponentDivisorSum δ X Y n hY f r ℒ s hs) x =
      ∑ᶠ C : irreducibleComponents X.left,
        toAlgebraicCycle (X.hom.relativeDimensionFunction δ) (n + (r : ℤ) - 1)
          ((@AlgebraicCycle.genericMultiplicity X.left
              (LocallyOfFiniteType.isLocallyNoetherian X.hom)
              (genericPoints.ofComponent C) : ℤ) •
            flatComponentDivisorCycle δ X Y n hY f r ℒ s hs C) x := rfl

/-- Flat pullback of the divisor cycle of a nonzero meromorphic section is the sum of its
divisor cycles on the reduced irreducible components of the source, weighted by their generic
multiplicities. -/
theorem flatPullback_divisor_eq_sum_components
    {S : Scheme.{u}} [UniversallyCatenary S] (δ : S → ℤ) [IsDimensionFunction δ]
    (X Y : Over S) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    [IsIntegral Y.left] (n : ℤ)
    (hY : Y.hom.relativeDimensionFunction δ (genericPoint Y.left) = n)
    (f : X ⟶ Y) (r : ℕ) [Flat f.left] [Scheme.Hom.RelativeDimension f.left r]
    (ℒ : Y.left.Modules) [Scheme.Modules.Invertible ℒ]
    (s : Y.left.toLocallyRingedSpace.meromorphicSections ℒ) (hs : s ≠ 0) :
    reindex (X.hom.relativeDimensionFunction δ) (flatDivisorDegree n r)
        (flatPullback δ X Y f r (n - 1)
          (relativeDivisorCycle Y.hom δ ℒ s hs (n - 1)
            (hY.trans (sub_add_cancel n 1).symm))) =
      flatComponentDivisorSum δ X Y n hY f r ℒ s hs := sorry

end AlgebraicGeometry.CycleGroup
