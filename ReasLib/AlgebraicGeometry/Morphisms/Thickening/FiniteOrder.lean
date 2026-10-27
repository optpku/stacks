/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import ReasLib.AlgebraicGeometry.Morphisms.Thickening
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Differentials

@[expose] public section

open CategoryTheory Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Thickening.Hom

private theorem isIso_residueFieldMap_of_isClosedImmersion {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsClosedImmersion f] (x : X) : IsIso (f.residueFieldMap x) := by
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  have h : Function.Surjective (Y.residue (f x) ≫ f.residueFieldMap x) := by
    rw [Scheme.residue_residueFieldMap]
    exact (X.residue_surjective x).comp (f.stalkMap_surjective x)
  exact Function.Surjective.of_comp (g := Y.residue (f x)) h

private theorem locallyQuasiFinite_of_isPullback {P X Y Z : Scheme.{u}}
    {i : P ⟶ X} {f : P ⟶ Y} {f' : X ⟶ Z} {j : Y ⟶ Z}
    (sq : IsPullback i f f' j) [IsClosedImmersion j] [Surjective j]
    (hf : LocallyQuasiFinite f) : LocallyQuasiFinite f' := by
  letI := hf
  apply LocallyQuasiFinite.of_fiberToSpecResidueField
  intro y
  obtain ⟨y, rfl⟩ := j.surjective y
  haveI := isIso_residueFieldMap_of_isClosedImmersion j y
  haveI : LocallyQuasiFinite (f.fiberToSpecResidueField y) :=
    inferInstanceAs (LocallyQuasiFinite (pullback.snd f (Y.fromSpecResidueField y)))
  haveI : IsIso (Spec.map (j.residueFieldMap y)) :=
    inferInstanceAs (IsIso (Scheme.Spec.map (j.residueFieldMap y).op))
  let sqf := isPullback_fiberToSpecResidueField_of_isPullback sq y
  haveI : IsIso sqf.cone.fst := sqf.isIso_fst_of_isIso
  apply (MorphismProperty.cancel_left_of_respectsIso @LocallyQuasiFinite
    sqf.cone.fst (f'.fiberToSpecResidueField (j y))).mp
  have hcomp : LocallyQuasiFinite
      (f.fiberToSpecResidueField y ≫ Spec.map (j.residueFieldMap y)) :=
    MorphismProperty.comp_mem @LocallyQuasiFinite _ _ inferInstance
      (MorphismProperty.of_isIso @LocallyQuasiFinite _)
  exact sqf.w.symm ▸ hcomp

private theorem nonempty_fiberHomeomorph_of_isPullback {P X Y Z : Scheme.{u}}
    {i : P ⟶ X} {f : P ⟶ Y} {f' : X ⟶ Z} {j : Y ⟶ Z}
    (sq : IsPullback i f f' j) [IsClosedImmersion j] (y : Y) :
    Nonempty (f.fiber y ≃ₜ f'.fiber (j y)) := by
  haveI := isIso_residueFieldMap_of_isClosedImmersion j y
  let sqf := isPullback_fiberToSpecResidueField_of_isPullback sq y
  haveI : IsIso sqf.cone.fst := sqf.isIso_fst_of_isIso
  exact ⟨sqf.cone.fst.homeomorph⟩

private theorem equidimensionalSpace_of_homeomorph {X Y : Type u}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₜ Y)
    (h : TopologicalSpace.EquidimensionalSpace X) :
    TopologicalSpace.EquidimensionalSpace Y := by
  have hpre (Z : irreducibleComponents Y) :
      e ⁻¹' (Z : Set Y) ∈ irreducibleComponents X := by
    apply preimage_mem_irreducibleComponents Z.property e.isOpenEmbedding
    simpa [Set.range_eq_univ.mpr e.surjective] using Z.property.1.1
  constructor
  intro Z₁ Z₂
  let e₁ : (e ⁻¹' (Z₁ : Set Y)) ≃ₜ Z₁ := e.subtype fun _ ↦ Iff.rfl
  let e₂ : (e ⁻¹' (Z₂ : Set Y)) ≃ₜ Z₂ := e.subtype fun _ ↦ Iff.rfl
  exact (IsHomeomorph.topologicalKrullDim_eq e₁ e₁.isHomeomorph).symm.trans
    ((h.topologicalKrullDim_eq ⟨_, hpre Z₁⟩ ⟨_, hpre Z₂⟩).trans
      (IsHomeomorph.topologicalKrullDim_eq e₂ e₂.isHomeomorph))

private theorem mono_of_isPullback {P X Y Z : Scheme.{u}}
    {i : P ⟶ X} {f : P ⟶ Y} {f' : X ⟶ Z} {j : Y ⟶ Z}
    (sq : IsPullback i f f' j) [IsFiniteOrderThickening j] [Mono f]
    [FormallyUnramified f'] : Mono f' := by
  letI : IsClosedImmersion j := IsFiniteOrderThickening.isClosedImmersion
  constructor
  intro W a b hab
  let a₀ := sq.lift (pullback.snd j (a ≫ f') ≫ a) (pullback.fst j (a ≫ f'))
    (by rw [Category.assoc, pullback.condition])
  let b₀ := sq.lift (pullback.snd j (a ≫ f') ≫ b) (pullback.fst j (a ≫ f'))
    (by rw [Category.assoc, ← hab, pullback.condition])
  have h₀ : a₀ = b₀ := (cancel_mono f).mp (by simp [a₀, b₀])
  have hi : pullback.snd j (a ≫ f') ≫ a = pullback.snd j (a ≫ f') ≫ b := by
    simpa only [a₀, b₀, IsPullback.lift_fst] using congrArg (fun m ↦ m ≫ i) h₀
  have hn : IsNilpotent (pullback.snd j (a ≫ f')).ker :=
    IsFiniteOrderThickening.ker_isNilpotent
  exact FormallyUnramified.hom_ext (pullback.snd j (a ≫ f')) hn f' hi hab

/-- In a cartesian morphism to a finite-order thickening, the closed and ambient maps are
simultaneously locally of finite type. -/
theorem locallyOfFiniteType_iff_of_isPullback {T U : Thickening.{u}} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom) [IsFiniteOrderThickening U.hom] :
    LocallyOfFiniteType g.left ↔ LocallyOfFiniteType g.right := sorry

set_option backward.isDefEq.respectTransparency false in
/-- In a cartesian morphism to a finite-order thickening, the closed and ambient maps are
simultaneously locally quasi-finite. -/
theorem locallyQuasiFinite_iff_of_isPullback {T U : Thickening.{u}} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom) [IsFiniteOrderThickening U.hom] :
    LocallyQuasiFinite g.left ↔ LocallyQuasiFinite g.right := by
  letI : IsClosedImmersion U.hom := U.prop.toIsClosedImmersion
  letI : Surjective U.hom := U.prop.toSurjective
  constructor
  · intro h
    exact locallyQuasiFinite_of_isPullback sq h
  · intro h
    exact MorphismProperty.of_isPullback sq h

set_option backward.isDefEq.respectTransparency false in
/-- In a cartesian morphism to a finite-order thickening, the closed and ambient maps have
relative dimension `d` simultaneously. -/
theorem relativeDimension_iff_of_isPullback {T U : Thickening.{u}} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom) [IsFiniteOrderThickening U.hom]
    (d : ℕ) :
    Scheme.Hom.RelativeDimension g.left d ↔ Scheme.Hom.RelativeDimension g.right d := by
  letI : IsClosedImmersion U.hom := U.prop.toIsClosedImmersion
  letI : Surjective U.hom := U.prop.toSurjective
  constructor
  · intro h
    refine
      { toLocallyOfFiniteType :=
          (locallyOfFiniteType_iff_of_isPullback g sq).mp h.toLocallyOfFiniteType
        equidimensionalSpace_fiber := ?_
        topologicalKrullDim_fiber := ?_ }
    · intro y hy
      obtain ⟨y, rfl⟩ := U.hom.surjective y
      obtain ⟨e⟩ := nonempty_fiberHomeomorph_of_isPullback sq y
      exact equidimensionalSpace_of_homeomorph e
        (h.equidimensionalSpace_fiber y (hy.map e.symm))
    · intro y hy
      obtain ⟨y, rfl⟩ := U.hom.surjective y
      obtain ⟨e⟩ := nonempty_fiberHomeomorph_of_isPullback sq y
      exact (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).symm.trans
        (h.topologicalKrullDim_fiber y (hy.map e.symm))
  · intro h
    refine
      { toLocallyOfFiniteType :=
          (locallyOfFiniteType_iff_of_isPullback g sq).mpr h.toLocallyOfFiniteType
        equidimensionalSpace_fiber := ?_
        topologicalKrullDim_fiber := ?_ }
    · intro y hy
      obtain ⟨e⟩ := nonempty_fiberHomeomorph_of_isPullback sq y
      exact equidimensionalSpace_of_homeomorph e.symm
        (h.equidimensionalSpace_fiber (U.hom y) (hy.map e))
    · intro y hy
      obtain ⟨e⟩ := nonempty_fiberHomeomorph_of_isPullback sq y
      exact (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).trans
        (h.topologicalKrullDim_fiber (U.hom y) (hy.map e))

/-- In a cartesian morphism to a finite-order thickening, the relative differential sheaves of
the closed and ambient maps vanish simultaneously. -/
theorem isZero_relativeDifferentials_iff_of_isPullback {T U : Thickening.{u}} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom) [IsFiniteOrderThickening U.hom] :
    IsZero (Ω[g.left.toShHom]) ↔ IsZero (Ω[g.right.toShHom]) := sorry

/-- In a cartesian morphism to a finite-order thickening, the closed and ambient maps are
simultaneously unramified. -/
theorem unramified_iff_of_isPullback {T U : Thickening.{u}} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom) [IsFiniteOrderThickening U.hom] :
    Unramified g.left ↔ Unramified g.right := by
  rw [unramified_iff_locallyOfFiniteType_and_isZero_relativeDifferentials,
    unramified_iff_locallyOfFiniteType_and_isZero_relativeDifferentials,
    locallyOfFiniteType_iff_of_isPullback g sq,
    isZero_relativeDifferentials_iff_of_isPullback g sq]

/-- In a cartesian morphism to a finite-order thickening, the closed and ambient maps are
simultaneously proper. -/
theorem isProper_iff_of_isPullback {T U : Thickening.{u}} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom) [IsFiniteOrderThickening U.hom] :
    IsProper g.left ↔ IsProper g.right := by
  rw [isProper_iff, isProper_iff, isSeparated_iff g, universallyClosed_iff g,
    locallyOfFiniteType_iff_of_isPullback g sq]

/-- In a cartesian morphism to a finite-order thickening, the closed and ambient maps are
simultaneously finite. -/
theorem isFinite_iff_of_isPullback {T U : Thickening.{u}} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom) [IsFiniteOrderThickening U.hom] :
    IsFinite g.left ↔ IsFinite g.right := by
  rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType,
    IsFinite.iff_isIntegralHom_and_locallyOfFiniteType, isIntegralHom_iff g,
    locallyOfFiniteType_iff_of_isPullback g sq]

set_option backward.isDefEq.respectTransparency false in
/-- In a cartesian morphism to a finite-order thickening, the closed and ambient maps are
simultaneously monomorphisms. -/
theorem mono_iff_of_isPullback {T U : Thickening.{u}} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom) [IsFiniteOrderThickening U.hom] :
    Mono g.left ↔ Mono g.right := by
  constructor
  · intro h
    letI : Mono g.left := h
    have hz : IsZero (Ω[g.left.toShHom]) :=
      (formallyUnramified_iff_isZero_relativeDifferentials g.left).mp inferInstance
    letI : FormallyUnramified g.right :=
      (formallyUnramified_iff_isZero_relativeDifferentials g.right).mpr
        ((isZero_relativeDifferentials_iff_of_isPullback g sq).mp hz)
    exact mono_of_isPullback sq
  · intro h
    exact sq.mono_snd_of_mono h

/-- In a cartesian morphism to a finite-order thickening, the closed and ambient maps are
simultaneously closed immersions. -/
theorem isClosedImmersion_iff_of_isPullback {T U : Thickening.{u}} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom) [IsFiniteOrderThickening U.hom] :
    IsClosedImmersion g.left ↔ IsClosedImmersion g.right := by
  rw [IsClosedImmersion.iff_isFinite_and_mono, IsClosedImmersion.iff_isFinite_and_mono,
    isFinite_iff_of_isPullback g sq, mono_iff_of_isPullback g sq]

set_option backward.isDefEq.respectTransparency false in
/-- In a cartesian morphism to a finite-order thickening, the closed and ambient maps are
simultaneously immersions. -/
theorem isImmersion_iff_of_isPullback {T U : Thickening.{u}} (g : T ⟶ U)
    (sq : IsPullback T.hom g.left g.right U.hom) [IsFiniteOrderThickening U.hom] :
    IsImmersion g.left ↔ IsImmersion g.right := by
  letI : IsClosedImmersion T.hom := T.prop.toIsClosedImmersion
  letI : Surjective T.hom := T.prop.toSurjective
  letI : IsClosedImmersion U.hom := U.prop.toIsClosedImmersion
  letI : Surjective U.hom := U.prop.toSurjective
  constructor
  · intro h
    letI := h
    have hj : IsHomeomorph U.hom :=
      isHomeomorph_iff_isEmbedding_surjective.mpr
        ⟨U.hom.isEmbedding, U.hom.surjective⟩
    let V : U.right.Opens :=
      ⟨U.hom '' (g.left.coborderRange : Set U.left),
        hj.isOpenMap _ g.left.coborderRange.isOpen⟩
    have hr : Set.range g.right ⊆ Set.range V.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      obtain ⟨x, rfl⟩ := T.hom.surjective x
      refine ⟨g.left x, subset_coborder ⟨x, rfl⟩, ?_⟩
      change (g.left ≫ U.hom) x = (T.hom ≫ g.right) x
      exact congrArg (fun m : T.left ⟶ U.right ↦ m x) sq.w.symm
    let fV : T.right ⟶ V := IsOpenImmersion.lift V.ι g.right hr
    have hfV : fV ≫ V.ι = g.right := IsOpenImmersion.lift_fac _ _ _
    let f₀ : T.left ⟶ pullback U.hom V.ι :=
      pullback.lift g.left (T.hom ≫ fV) (by rw [Category.assoc, hfV]; exact sq.w.symm)
    have hfst : Set.range (pullback.fst U.hom V.ι) =
        Set.range g.left.coborderRange.ι := by
      rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
      exact Set.preimage_image_eq _ U.hom.isEmbedding.injective
    let e := IsOpenImmersion.isoOfRangeEq (pullback.fst U.hom V.ι)
      g.left.coborderRange.ι hfst
    have he : f₀ ≫ e.hom = g.left.liftCoborder := by
      apply (cancel_mono g.left.coborderRange.ι).mp
      simp [Category.assoc, e, f₀]
    have hc : IsClosedImmersion f₀ :=
      (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion f₀ e.hom).mp
        (he.symm ▸ (inferInstance : IsClosedImmersion g.left.liftCoborder))
    letI : IsThickening (pullback.snd U.hom V.ι) :=
      { toIsClosedImmersion := inferInstance
        toSurjective := inferInstance }
    let gV : T ⟶ Thickening.of (pullback.snd U.hom V.ι) :=
      Thickening.homMk f₀ fV (by
        change f₀ ≫ pullback.snd U.hom V.ι = T.hom ≫ fV
        exact pullback.lift_snd _ _ _)
    have sqV : IsPullback T.hom gV.left gV.right
        (Thickening.of (pullback.snd U.hom V.ι)).hom := by
      change IsPullback T.hom f₀ fV (pullback.snd U.hom V.ι)
      apply IsPullback.of_bot ?_ (by simp [f₀]) (IsPullback.of_hasPullback U.hom V.ι).flip
      simpa only [f₀, pullback.lift_fst, hfV] using sq
    letI : IsFiniteOrderThickening (Thickening.of (pullback.snd U.hom V.ι)).hom :=
      inferInstanceAs (IsFiniteOrderThickening (pullback.snd U.hom V.ι))
    haveI : IsClosedImmersion fV :=
      (isClosedImmersion_iff_of_isPullback gV sqV).mp hc
    rw [← hfV]
    infer_instance
  · intro h
    exact MorphismProperty.of_isPullback sq h

end AlgebraicGeometry.Thickening.Hom
