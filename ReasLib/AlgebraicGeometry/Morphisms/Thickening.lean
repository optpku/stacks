/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.QuasiAffine.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Thickening.Hom

private theorem quasiCompact_of_comp_surjective {X Y Z : Scheme.{u}}
    (i : X ⟶ Y) (f : Y ⟶ Z) [Surjective i] [QuasiCompact (i ≫ f)] :
    QuasiCompact f := by
  constructor
  intro V hVo hVc
  have hc := QuasiCompact.isCompact_preimage (f := i ≫ f) V hVo hVc
  have he : i '' ((i ≫ f) ⁻¹' V) = f ⁻¹' V := by
    simpa only [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp] using
      Set.image_preimage_eq (f ⁻¹' V) i.surjective
  rw [← he]
  exact hc.image i.continuous

private theorem diagonal_property_of_comp_surjective
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderComposition] [P.IsStableUnderBaseChange]
    (hdesc : ∀ {X Y Z : Scheme.{u}} (i : X ⟶ Y) (f : Y ⟶ Z),
      Surjective i → P (i ≫ f) → P f)
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) (f : Y ⟶ Z) [Surjective i]
    (hi : P i) (hif : P (Limits.pullback.diagonal (i ≫ f))) :
    P (Limits.pullback.diagonal f) := by
  let m := Limits.pullback.map (i ≫ f) (i ≫ f) f f i i (𝟙 Z)
    (Category.comp_id _) (Category.comp_id _)
  have hm : P m := MorphismProperty.pullbackMap (P := P) hi hi rfl rfl
  have hw : Limits.pullback.diagonal (i ≫ f) ≫ m = i ≫ Limits.pullback.diagonal f := by
    apply Limits.pullback.hom_ext
    · simp [m]
    · simp [m]
  apply hdesc i (Limits.pullback.diagonal f) inferInstance
  rw [← hw]
  exact P.comp_mem _ _ hif hm

private theorem universallyInjective_of_comp_surjective {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Surjective f] [UniversallyInjective (f ≫ g)] :
    UniversallyInjective g := by
  constructor
  intro X' Y' i₁ i₂ g' H
  have h := UniversallyInjective.universally_injective _ _ _
    ((IsPullback.of_hasPullback i₁ f).paste_horiz H)
  change Function.Injective (g' ∘ Limits.pullback.fst i₁ f) at h
  exact h.of_comp_right
    (MorphismProperty.pullback_fst (P := @Surjective) i₁ f inferInstance).surj

private theorem universallyOpen_of_comp_surjective {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Surjective f] [UniversallyOpen (f ≫ g)] :
    UniversallyOpen g := by
  constructor
  intro X' Y' i₁ i₂ g' H
  have h := UniversallyOpen.universally_isOpenMap _ _ _
    ((IsPullback.of_hasPullback i₁ f).paste_horiz H)
  exact IsOpenMap.of_comp (Scheme.Hom.continuous _)
    (MorphismProperty.pullback_fst (P := @Surjective) _ _ inferInstance).surj h

private theorem universallyOpen_of_surjective_closedImmersion {X Y : Scheme.{u}}
    (i : X ⟶ Y) [IsClosedImmersion i] [Surjective i] : UniversallyOpen i := by
  constructor
  intro X' Y' i₁ i₂ i' H
  haveI : IsClosedImmersion i' := MorphismProperty.of_isPullback H.flip inferInstance
  haveI : Surjective i' := MorphismProperty.of_isPullback H.flip inferInstance
  exact (i'.isClosedEmbedding.isEmbedding.isOpenEmbedding_of_surjective i'.surjective).isOpenMap

/-- The closed and ambient maps of a morphism of thickenings are simultaneously affine. -/
theorem isAffineHom_iff {T U : Thickening.{u}} (g : T ⟶ U) :
    IsAffineHom g.left ↔ IsAffineHom g.right := sorry

/-- The closed and ambient maps of a morphism of thickenings are simultaneously surjective. -/
theorem surjective_iff {T U : Thickening.{u}} (g : T ⟶ U) :
    Surjective g.left ↔ Surjective g.right := by
  letI : IsThickening T.hom := T.prop
  letI : IsThickening U.hom := U.prop
  have hw : g.left ≫ U.hom = T.hom ≫ g.right := g.hom.w
  constructor
  · intro h
    haveI := h
    haveI : Surjective (T.hom ≫ g.right) := by
      rw [← hw]
      exact MorphismProperty.comp_mem @Surjective g.left U.hom h inferInstance
    exact Surjective.of_comp T.hom g.right
  · intro h
    haveI := h
    haveI : Surjective (g.left ≫ U.hom) := by
      rw [hw]
      exact MorphismProperty.comp_mem @Surjective T.hom g.right inferInstance h
    refine ⟨fun y ↦ ?_⟩
    obtain ⟨x, hx⟩ := (g.left ≫ U.hom).surjective (U.hom y)
    rw [Scheme.Hom.comp_apply] at hx
    exact ⟨x, U.hom.isClosedEmbedding.injective hx⟩

/-- The closed and ambient maps of a morphism of thickenings are simultaneously quasi-compact. -/
theorem quasiCompact_iff {T U : Thickening.{u}} (g : T ⟶ U) :
    QuasiCompact g.left ↔ QuasiCompact g.right := by
  letI : IsThickening T.hom := T.prop
  letI : IsThickening U.hom := U.prop
  have hw : g.left ≫ U.hom = T.hom ≫ g.right := g.hom.w
  constructor
  · intro h
    haveI := h
    haveI : QuasiCompact (T.hom ≫ g.right) := by
      rw [← hw]
      exact MorphismProperty.comp_mem @QuasiCompact g.left U.hom h inferInstance
    exact quasiCompact_of_comp_surjective T.hom g.right
  · intro h
    haveI := h
    have hc : QuasiCompact (g.left ≫ U.hom) := by
      rw [hw]
      exact MorphismProperty.comp_mem @QuasiCompact T.hom g.right inferInstance h
    exact MorphismProperty.of_postcomp (W := @QuasiCompact) (W' := @QuasiSeparated)
      g.left U.hom (inferInstance : QuasiSeparated U.hom) hc

/-- The closed and ambient maps of a morphism of thickenings are simultaneously universally
closed. -/
theorem universallyClosed_iff {T U : Thickening.{u}} (g : T ⟶ U) :
    UniversallyClosed g.left ↔ UniversallyClosed g.right := by
  letI : IsThickening T.hom := T.prop
  letI : IsThickening U.hom := U.prop
  have hw : g.left ≫ U.hom = T.hom ≫ g.right := g.hom.w
  constructor
  · intro h
    haveI := h
    haveI : UniversallyClosed (T.hom ≫ g.right) := by
      rw [← hw]
      exact MorphismProperty.comp_mem @UniversallyClosed g.left U.hom h inferInstance
    exact UniversallyClosed.of_comp_surjective T.hom g.right
  · intro h
    haveI := h
    have hc : UniversallyClosed (g.left ≫ U.hom) := by
      rw [hw]
      exact MorphismProperty.comp_mem @UniversallyClosed T.hom g.right inferInstance h
    exact MorphismProperty.of_postcomp (W := @UniversallyClosed)
      (W' := MorphismProperty.monomorphisms Scheme) g.left U.hom
      (inferInstance : Mono U.hom) hc

/-- The closed and ambient maps of a morphism of thickenings are simultaneously integral. -/
theorem isIntegralHom_iff {T U : Thickening.{u}} (g : T ⟶ U) :
    IsIntegralHom g.left ↔ IsIntegralHom g.right := by
  rw [IsIntegralHom.iff_universallyClosed_and_isAffineHom,
    IsIntegralHom.iff_universallyClosed_and_isAffineHom]
  exact and_congr (universallyClosed_iff g) (isAffineHom_iff g)

/-- The closed and ambient maps of a morphism of thickenings are simultaneously separated. -/
theorem isSeparated_iff {T U : Thickening.{u}} (g : T ⟶ U) :
    IsSeparated g.left ↔ IsSeparated g.right := by
  letI : IsThickening T.hom := T.prop
  letI : IsThickening U.hom := U.prop
  have hw : g.left ≫ U.hom = T.hom ≫ g.right := g.hom.w
  constructor
  · intro h
    haveI : IsSeparated (T.hom ≫ g.right) := by
      rw [← hw]
      exact MorphismProperty.comp_mem @IsSeparated g.left U.hom h inferInstance
    haveI : UniversallyClosed (Limits.pullback.diagonal g.right) :=
      diagonal_property_of_comp_surjective @UniversallyClosed
        (fun i f hi hif ↦ by
          haveI := hi
          haveI := hif
          exact UniversallyClosed.of_comp_surjective i f)
        T.hom g.right inferInstance inferInstance
    exact ⟨IsClosedImmersion.of_isPreimmersion _
      (Limits.pullback.diagonal g.right).isClosedMap.isClosed_range⟩
  · intro h
    haveI : IsSeparated (g.left ≫ U.hom) := by
      rw [hw]
      exact MorphismProperty.comp_mem @IsSeparated T.hom g.right inferInstance h
    exact IsSeparated.of_comp g.left U.hom

/-- The closed and ambient maps of a morphism of thickenings are simultaneously
quasi-separated. -/
theorem quasiSeparated_iff {T U : Thickening.{u}} (g : T ⟶ U) :
    QuasiSeparated g.left ↔ QuasiSeparated g.right := by
  letI : IsThickening T.hom := T.prop
  letI : IsThickening U.hom := U.prop
  have hw : g.left ≫ U.hom = T.hom ≫ g.right := g.hom.w
  constructor
  · intro h
    haveI : QuasiSeparated (T.hom ≫ g.right) := by
      rw [← hw]
      exact MorphismProperty.comp_mem @QuasiSeparated g.left U.hom h inferInstance
    constructor
    exact diagonal_property_of_comp_surjective @QuasiCompact
      (fun i f hi hif ↦ by
        haveI := hi
        haveI := hif
        exact quasiCompact_of_comp_surjective i f)
      T.hom g.right inferInstance inferInstance
  · intro h
    haveI : QuasiSeparated (g.left ≫ U.hom) := by
      rw [hw]
      exact MorphismProperty.comp_mem @QuasiSeparated T.hom g.right inferInstance h
    exact QuasiSeparated.of_comp g.left U.hom

/-- The closed and ambient maps of a morphism of thickenings are simultaneously universally
injective. -/
theorem universallyInjective_iff {T U : Thickening.{u}} (g : T ⟶ U) :
    UniversallyInjective g.left ↔ UniversallyInjective g.right := by
  letI : IsThickening T.hom := T.prop
  letI : IsThickening U.hom := U.prop
  have hw : g.left ≫ U.hom = T.hom ≫ g.right := g.hom.w
  constructor
  · intro h
    haveI : UniversallyInjective (T.hom ≫ g.right) := by
      rw [← hw]
      exact MorphismProperty.comp_mem @UniversallyInjective g.left U.hom h inferInstance
    exact universallyInjective_of_comp_surjective T.hom g.right
  · intro h
    have hc : UniversallyInjective (g.left ≫ U.hom) := by
      rw [hw]
      exact MorphismProperty.comp_mem @UniversallyInjective T.hom g.right inferInstance h
    exact MorphismProperty.of_postcomp (W := @UniversallyInjective)
      (W' := MorphismProperty.monomorphisms Scheme) g.left U.hom
      (inferInstance : Mono U.hom) hc

/-- The closed and ambient maps of a morphism of thickenings are simultaneously universally
open. -/
theorem universallyOpen_iff {T U : Thickening.{u}} (g : T ⟶ U) :
    UniversallyOpen g.left ↔ UniversallyOpen g.right := by
  letI : IsThickening T.hom := T.prop
  letI : IsThickening U.hom := U.prop
  haveI : UniversallyOpen T.hom := universallyOpen_of_surjective_closedImmersion T.hom
  haveI : UniversallyOpen U.hom := universallyOpen_of_surjective_closedImmersion U.hom
  have hw : g.left ≫ U.hom = T.hom ≫ g.right := g.hom.w
  constructor
  · intro h
    haveI := h
    haveI : UniversallyOpen (T.hom ≫ g.right) := by
      rw [← hw]
      exact MorphismProperty.comp_mem @UniversallyOpen g.left U.hom h inferInstance
    exact universallyOpen_of_comp_surjective T.hom g.right
  · intro h
    haveI := h
    have hc : UniversallyOpen (g.left ≫ U.hom) := by
      rw [hw]
      exact MorphismProperty.comp_mem @UniversallyOpen T.hom g.right inferInstance h
    exact MorphismProperty.of_postcomp (W := @UniversallyOpen)
      (W' := MorphismProperty.monomorphisms Scheme) g.left U.hom
      (inferInstance : Mono U.hom) hc

/-- The closed and ambient maps of a morphism of thickenings are simultaneously quasi-affine. -/
theorem quasiAffineHom_iff {T U : Thickening.{u}} (g : T ⟶ U) :
    QuasiAffineHom g.left ↔ QuasiAffineHom g.right := sorry

end AlgebraicGeometry.Thickening.Hom
