/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import ReasLib.AlgebraicGeometry.Morphisms.Thickening
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Differentials

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Thickening.Hom

set_option backward.isDefEq.respectTransparency false in
/-- In a cartesian morphism of thickenings whose horizontal maps are locally of finite type,
the closed map is locally quasi-finite if and only if the ambient map is locally quasi-finite. -/
theorem locallyQuasiFinite_iff {T U : Thickening.{u}} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    LocallyQuasiFinite g.left ↔ LocallyQuasiFinite g.right := by
  letI : IsThickening T.hom := T.prop
  letI : IsThickening U.hom := U.prop
  have hw (x : T.left) : U.hom (g.left x) = g.right (T.hom x) :=
    congrArg (fun m : T.left ⟶ U.right ↦ m x) g.hom.w
  constructor
  · intro h
    letI := h
    apply locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr
    intro y
    obtain ⟨y, rfl⟩ := U.hom.surjective y
    have hfiber : T.hom '' (g.left ⁻¹' {y}) = g.right ⁻¹' {U.hom y} := by
      ext x'
      constructor
      · rintro ⟨x, hx, rfl⟩
        change g.left x = y at hx
        change g.right (T.hom x) = U.hom y
        exact (hw x).symm.trans (congrArg U.hom hx)
      · intro hx
        obtain ⟨x, rfl⟩ := T.hom.surjective x'
        refine ⟨x, ?_, rfl⟩
        change g.left x = y
        apply U.hom.isClosedEmbedding.injective
        exact (hw x).trans hx
    rw [← hfiber]
    exact (g.left.isDiscrete_preimage_singleton y).image T.hom.isEmbedding.toIsInducing
  · intro h
    exact MorphismProperty.of_isPullback hcart.flip h

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of finite type,
the closed map is finite if and only if the ambient map is finite. -/
theorem isFinite_iff {T U : Thickening.{u}} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    IsFinite g.left ↔ IsFinite g.right := by
  rw [IsFinite.iff_isProper_and_locallyQuasiFinite,
    IsFinite.iff_isProper_and_locallyQuasiFinite,
    AlgebraicGeometry.isProper_iff, AlgebraicGeometry.isProper_iff,
    isSeparated_iff g, universallyClosed_iff g, locallyQuasiFinite_iff g hcart]
  simp [show LocallyOfFiniteType g.left from inferInstance,
    show LocallyOfFiniteType g.right from inferInstance]

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of finite type,
the closed map is a closed immersion if and only if the ambient map is a closed immersion. -/
theorem isClosedImmersion_iff {T U : Thickening.{u}} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    IsClosedImmersion g.left ↔ IsClosedImmersion g.right := sorry

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of finite type,
the relative differentials of the closed map vanish if and only if those of the ambient map
vanish. -/
theorem isZero_relativeDifferentials_iff {T U : Thickening.{u}} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    Limits.IsZero (Ω[g.left.toShHom]) ↔ Limits.IsZero (Ω[g.right.toShHom]) := sorry

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of finite type,
the closed map is unramified if and only if the ambient map is unramified. -/
theorem unramified_iff {T U : Thickening.{u}} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    Unramified g.left ↔ Unramified g.right := by
  constructor
  · intro h
    refine { toFormallyUnramified := ?_, toLocallyOfFiniteType := inferInstance }
    apply (formallyUnramified_iff_isZero_relativeDifferentials g.right).mpr
    apply (isZero_relativeDifferentials_iff g hcart).mp
    exact (formallyUnramified_iff_isZero_relativeDifferentials g.left).mp
      h.toFormallyUnramified
  · intro h
    refine { toFormallyUnramified := ?_, toLocallyOfFiniteType := inferInstance }
    apply (formallyUnramified_iff_isZero_relativeDifferentials g.left).mpr
    apply (isZero_relativeDifferentials_iff g hcart).mpr
    exact (formallyUnramified_iff_isZero_relativeDifferentials g.right).mp
      h.toFormallyUnramified

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of finite type,
the closed map is a monomorphism if and only if the ambient map is a monomorphism. -/
theorem mono_iff {T U : Thickening.{u}} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    Mono g.left ↔ Mono g.right := by
  constructor
  · intro h
    letI := h
    have hleft : Unramified g.left :=
      { toFormallyUnramified := inferInstance, toLocallyOfFiniteType := inferInstance }
    letI : FormallyUnramified g.right :=
      ((unramified_iff g hcart).mp hleft).toFormallyUnramified
    haveI : UniversallyInjective g.right := (universallyInjective_iff g).mp inferInstance
    haveI : Surjective (Limits.pullback.diagonal g.right) :=
      (UniversallyInjective.iff_diagonal g.right).mp inferInstance
    haveI : Epi (Limits.pullback.diagonal g.right).base :=
      ConcreteCategory.epi_of_surjective _ (Limits.pullback.diagonal g.right).surjective
    haveI : IsIso (Limits.pullback.diagonal g.right) :=
      IsOpenImmersion.isIso _
    exact (Limits.pullback.isIso_diagonal_iff g.right).mp inferInstance
  · intro h
    exact hcart.mono_fst_of_mono h

set_option backward.isDefEq.respectTransparency false in
/-- In a cartesian morphism of thickenings whose horizontal maps are locally of finite type,
the closed map is an immersion if and only if the ambient map is an immersion. -/
theorem isImmersion_iff {T U : Thickening.{u}} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
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
      exact congrArg (fun m : T.left ⟶ U.right ↦ m x) g.hom.w
    let fV : T.right ⟶ V := IsOpenImmersion.lift V.ι g.right hr
    have hfV : fV ≫ V.ι = g.right := IsOpenImmersion.lift_fac _ _ _
    let f₀ : T.left ⟶ Limits.pullback U.hom V.ι :=
      Limits.pullback.lift g.left (T.hom ≫ fV)
        (by rw [Category.assoc, hfV]; exact g.hom.w)
    have hfst : Set.range (Limits.pullback.fst U.hom V.ι) =
        Set.range g.left.coborderRange.ι := by
      rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
      exact Set.preimage_image_eq _ U.hom.isEmbedding.injective
    let e := IsOpenImmersion.isoOfRangeEq (Limits.pullback.fst U.hom V.ι)
      g.left.coborderRange.ι hfst
    have he : f₀ ≫ e.hom = g.left.liftCoborder := by
      apply (cancel_mono g.left.coborderRange.ι).mp
      simp [Category.assoc, e, f₀]
    have hc : IsClosedImmersion f₀ :=
      (MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion f₀ e.hom).mp
        (he.symm ▸ (inferInstance : IsClosedImmersion g.left.liftCoborder))
    letI : IsThickening (Limits.pullback.snd U.hom V.ι) :=
      { toIsClosedImmersion := inferInstance
        toSurjective := inferInstance }
    let gV : T ⟶ Thickening.of (Limits.pullback.snd U.hom V.ι) :=
      Thickening.homMk f₀ fV (Limits.pullback.lift_snd _ _ _)
    have sqV : IsPullback T.hom gV.left gV.right
        (Thickening.of (Limits.pullback.snd U.hom V.ι)).hom := by
      change IsPullback T.hom f₀ fV (Limits.pullback.snd U.hom V.ι)
      apply IsPullback.of_bot ?_ (by simp [f₀])
        (IsPullback.of_hasPullback U.hom V.ι).flip
      simpa only [f₀, Limits.pullback.lift_fst, hfV] using hcart.flip
    letI : IsClosedImmersion f₀ := hc
    letI : LocallyOfFiniteType fV := by
      haveI : LocallyOfFiniteType (fV ≫ V.ι) := hfV.symm ▸ inferInstance
      exact locallyOfFiniteType_of_comp fV V.ι
    letI : LocallyOfFiniteType gV.left := by
      change LocallyOfFiniteType f₀
      infer_instance
    letI : LocallyOfFiniteType gV.right := by
      change LocallyOfFiniteType fV
      infer_instance
    haveI : IsClosedImmersion fV := (isClosedImmersion_iff gV sqV.flip).mp hc
    rw [← hfV]
    infer_instance
  · intro h
    exact MorphismProperty.of_isPullback hcart.flip h

/-- In a cartesian morphism of thickenings whose horizontal maps are locally of finite type,
the closed map is proper if and only if the ambient map is proper. -/
theorem isProper_iff {T U : Thickening.{u}} (g : T ⟶ U)
    [LocallyOfFiniteType g.left] [LocallyOfFiniteType g.right]
    (hcart : IsPullback g.left T.hom U.hom g.right) :
    IsProper g.left ↔ IsProper g.right := by
  rw [AlgebraicGeometry.isProper_iff, AlgebraicGeometry.isProper_iff,
    isSeparated_iff g, universallyClosed_iff g]
  simp [show LocallyOfFiniteType g.left from inferInstance,
    show LocallyOfFiniteType g.right from inferInstance]

end AlgebraicGeometry.Thickening.Hom
