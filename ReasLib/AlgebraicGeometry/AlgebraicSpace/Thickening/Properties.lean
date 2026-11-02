/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Thickening.Arrow
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyOpen
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.Characterization
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion.QuasiCompact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.QuasiCompact.Cancellation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiCompact.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.Cancellation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Integral
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Descent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.ClosedImmersion
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Separation.Cancellation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Affine.Diagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.AffineDescent
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyOpen.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IsScheme.Thickening
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Cancellation
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Closed.InverseImage

/-!
# Transfer of morphism properties along morphisms of thickenings

A morphism of thickenings of algebraic spaces over a scheme has a closed
map and an ambient map, and the listed morphism properties hold for one
if and only if they hold for the other.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Thickening.Hom

set_option backward.isDefEq.respectTransparency false

open Limits

/-- The closed and ambient maps of a morphism of thickenings are simultaneously
affine. -/
theorem affine_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U) :
    Affine g.left ↔ Affine g.right := by
  letI : IsThickening T.hom := T.prop
  letI : IsThickening U.hom := U.prop
  have hw : g.left ≫ U.hom = T.hom ≫ g.right := g.w
  constructor
  · intro h
    letI := h
    haveI : Affine (T.hom ≫ g.right) := by
      rw [← hw]
      infer_instance
    constructor
    intro Z _ P a pZ pX hp
    -- The base change of the source thickening is a finite surjection from an affine space.
    haveI : IsAffine (pullback T.hom pX) :=
      Affine.pullback_isAffine (f := T.hom ≫ g.right)
        ((IsPullback.of_hasPullback T.hom pX).flip.paste_horiz hp)
    exact IsAffine.of_isFinite_surjective (pullback.snd T.hom pX)
  · intro h
    letI := h
    haveI : Affine (g.left ≫ U.hom) := by
      rw [hw]
      infer_instance
    exact Affine.of_comp g.left U.hom

/-- The closed and ambient maps of a morphism of thickenings are simultaneously
surjective. -/
theorem surjective_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U) :
    Surjective g.left ↔ Surjective g.right := by
  letI : IsThickening T.hom := T.prop
  letI : IsThickening U.hom := U.prop
  have hw (x : Points T.left) :
      Points.map U.hom (Points.map g.left x) =
        Points.map g.right (Points.map T.hom x) := by
    simpa only [Points.map_comp] using congrArg (fun f ↦ Points.map f x)
      (show g.left ≫ U.hom = T.hom ≫ g.right from g.w)
  constructor
  · intro h
    refine ⟨fun y' ↦ ?_⟩
    obtain ⟨y, rfl⟩ := Surjective.map_surjective (f := U.hom) y'
    obtain ⟨x, hx⟩ := h.map_surjective y
    exact ⟨Points.map T.hom x, (hw x).symm.trans (congrArg (Points.map U.hom) hx)⟩
  · intro h
    refine ⟨fun y ↦ ?_⟩
    obtain ⟨x', hx'⟩ := h.map_surjective (Points.map U.hom y)
    obtain ⟨x, rfl⟩ := Surjective.map_surjective (f := T.hom) x'
    exact ⟨x, UniversallyInjective.map_injective (f := U.hom) ((hw x).trans hx')⟩

/-- The closed and ambient maps of a morphism of thickenings are simultaneously
quasi-compact. -/
theorem quasiCompact_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U) :
    QuasiCompact g.left ↔ QuasiCompact g.right := by
  letI : IsThickening T.hom := T.prop
  letI : IsThickening U.hom := U.prop
  have hw : g.left ≫ U.hom = T.hom ≫ g.right := g.w
  constructor
  · intro h
    letI := h
    haveI : QuasiCompact (T.hom ≫ g.right) := by
      rw [← hw]
      infer_instance
    exact QuasiCompact.of_comp_surjective T.hom g.right
  · intro h
    letI := h
    haveI : QuasiCompact (g.left ≫ U.hom) := by
      rw [hw]
      infer_instance
    exact QuasiCompact.of_comp g.left U.hom

/-- The closed and ambient maps of a morphism of thickenings are simultaneously
universally closed. -/
theorem universallyClosed_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U) :
    UniversallyClosed g.left ↔ UniversallyClosed g.right := by
  letI : IsThickening T.hom := T.prop
  letI : IsThickening U.hom := U.prop
  have hw : g.left ≫ U.hom = T.hom ≫ g.right := g.w
  constructor
  · intro h
    letI := h
    haveI : UniversallyClosed (T.hom ≫ g.right) := by
      rw [← hw]
      infer_instance
    exact UniversallyClosed.of_comp_surjective T.hom g.right
  · intro h
    letI := h
    haveI : UniversallyClosed (g.left ≫ U.hom) := by
      rw [hw]
      infer_instance
    exact UniversallyClosed.of_comp g.left U.hom

/-- The closed and ambient maps of a morphism of thickenings are simultaneously
integral. -/
theorem isIntegralHom_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U) :
    IsIntegralHom g.left ↔ IsIntegralHom g.right := by
  rw [IsIntegralHom.iff_universallyClosed_and_affine,
    IsIntegralHom.iff_universallyClosed_and_affine,
    universallyClosed_iff g, affine_iff g]

/-- The closed and ambient maps of a morphism of thickenings are simultaneously
separated. -/
theorem separated_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U) :
    Separated g.left ↔ Separated g.right := by
  letI : IsThickening T.hom := T.prop
  letI : IsThickening U.hom := U.prop
  have hw : g.left ≫ U.hom = T.hom ≫ g.right := g.w
  constructor
  · intro h
    letI := h
    haveI : Separated (T.hom ≫ g.right) := by
      rw [← hw]
      infer_instance
    exact Separated.of_comp_surjective_universallyClosed T.hom g.right
  · intro h
    letI := h
    haveI : Separated (g.left ≫ U.hom) := by
      rw [hw]
      infer_instance
    exact Separated.of_comp g.left U.hom

/-- The closed and ambient maps of a morphism of thickenings are simultaneously
quasi-separated. -/
theorem quasiSeparated_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U) :
    QuasiSeparated g.left ↔ QuasiSeparated g.right := by
  letI : IsThickening T.hom := T.prop
  letI : IsThickening U.hom := U.prop
  have hw : g.left ≫ U.hom = T.hom ≫ g.right := g.w
  constructor
  · intro h
    letI := h
    haveI : QuasiSeparated (T.hom ≫ g.right) := by
      rw [← hw]
      infer_instance
    exact QuasiSeparated.of_comp_surjective_universallyClosed T.hom g.right
  · intro h
    letI := h
    haveI : QuasiSeparated (g.left ≫ U.hom) := by
      rw [hw]
      infer_instance
    exact QuasiSeparated.of_comp g.left U.hom

/-- The closed and ambient maps of a morphism of thickenings are simultaneously
universally injective. -/
theorem universallyInjective_iff {S : Scheme.{u}} {T U : Thickening S}
    (g : T ⟶ U) :
    UniversallyInjective g.left ↔ UniversallyInjective g.right := by
  letI : IsThickening T.hom := T.prop
  letI : IsThickening U.hom := U.prop
  have hw : g.left ≫ U.hom = T.hom ≫ g.right := g.w
  constructor
  · intro h
    letI := h
    haveI : UniversallyInjective (T.hom ≫ g.right) := by
      rw [← hw]
      infer_instance
    constructor
    intro P Z a b f hp
    have hi : Function.Injective (Points.map (pullback.snd T.hom a ≫ f)) :=
      UniversallyInjective.universally_injective (f := T.hom ≫ g.right) _ _ _
        ((IsPullback.of_hasPullback T.hom a).flip.paste_horiz hp)
    intro x y hxy
    obtain ⟨x, rfl⟩ := Surjective.map_surjective (f := pullback.snd T.hom a) x
    obtain ⟨y, rfl⟩ := Surjective.map_surjective (f := pullback.snd T.hom a) y
    apply congrArg (Points.map (pullback.snd T.hom a))
    apply hi
    simpa only [Points.map_comp] using hxy
  · intro h
    letI := h
    apply MorphismProperty.of_postcomp
      (@UniversallyInjective S : MorphismProperty (AlgebraicSpace S)) g.left U.hom
      (show Mono U.hom from inferInstance)
    rw [hw]
    infer_instance

/-- The closed and ambient maps of a morphism of thickenings are simultaneously
universally open. -/
theorem universallyOpen_iff {S : Scheme.{u}} {T U : Thickening S} (g : T ⟶ U) :
    UniversallyOpen g.left ↔ UniversallyOpen g.right := by
  letI : IsThickening T.hom := T.prop
  letI : IsThickening U.hom := U.prop
  have ho {X Y : AlgebraicSpace S} (i : X ⟶ Y) [IsThickening i] :
      UniversallyOpen i := by
    constructor
    intro P Z a b f hp
    -- Every base change of a thickening is closed and bijective on points, hence open.
    have hc : IsClosedMap (Points.map f) :=
      UniversallyClosed.universally_isClosedMap (f := i) _ _ _ hp
    have hi : Function.Injective (Points.map f) :=
      UniversallyInjective.universally_injective (f := i) _ _ _ hp
    haveI : Surjective f := Surjective.of_isPullback hp.flip inferInstance
    have hb : Function.Bijective (Points.map f) := ⟨hi, Surjective.map_surjective⟩
    intro s hs
    rw [← isClosed_compl_iff, ← Set.image_compl_eq hb]
    exact hc _ hs.isClosed_compl
  letI : UniversallyOpen T.hom := ho T.hom
  letI : UniversallyOpen U.hom := ho U.hom
  have hw : g.left ≫ U.hom = T.hom ≫ g.right := g.w
  constructor
  · intro h
    letI := h
    haveI : UniversallyOpen (T.hom ≫ g.right) := by
      rw [← hw]
      infer_instance
    constructor
    intro P Z a b f hp
    have hc : IsOpenMap (Points.map (pullback.snd T.hom a ≫ f)) :=
      UniversallyOpen.universally_isOpenMap (f := T.hom ≫ g.right) _ _ _
        ((IsPullback.of_hasPullback T.hom a).flip.paste_horiz hp)
    apply IsOpenMap.of_comp (Points.continuous_map (pullback.snd T.hom a))
      (Surjective.map_surjective (f := pullback.snd T.hom a))
    simpa only [Function.comp_def, ← Points.map_comp] using hc
  · intro h
    letI := h
    apply MorphismProperty.of_postcomp
      (@UniversallyOpen S : MorphismProperty (AlgebraicSpace S)) g.left U.hom
      (show Mono U.hom from inferInstance)
    rw [hw]
    infer_instance

/-- The closed and ambient maps of a morphism of thickenings are simultaneously
representable. -/
theorem relativelyRepresentable_iff {S : Scheme.{u}} {T U : Thickening S}
    (g : T ⟶ U) :
    yoneda.relativelyRepresentable g.left ↔
      yoneda.relativelyRepresentable g.right := by
  letI : IsThickening T.hom := T.prop
  letI : IsThickening U.hom := U.prop
  have hw : g.left ≫ U.hom = T.hom ≫ g.right := g.w
  have hw' : (g.left : T.left.functorOfPoints ⟶ U.left.functorOfPoints) ≫ U.hom =
      (T.hom : T.left.functorOfPoints ⟶ T.right.functorOfPoints) ≫ g.right := hw
  constructor
  · intro h
    have hc : yoneda.relativelyRepresentable
        (T.hom ≫ g.right : T.left.functorOfPoints ⟶ U.right.functorOfPoints) := by
      exact hw' ▸ MorphismProperty.comp_mem yoneda.relativelyRepresentable
        g.left U.hom h (IsClosedImmersion.presheaf (f := U.hom)).rep
    intro Z a
    let a' : ofOver Z ⟶ U.right := a
    -- Form the test pullback and then its thickening by the closed source.
    let P := ReasLibPullback.pullbackOver g.right a'
      U.right.isSheaf U.right.representableDiagonal
    let pX : P ⟶ T.right := ReasLibPullback.pullbackOverFst g.right a'
      U.right.isSheaf U.right.representableDiagonal
    let pZ : P ⟶ ofOver Z := ReasLibPullback.pullbackOverSnd g.right a'
      U.right.isSheaf U.right.representableDiagonal
    let Q := ReasLibPullback.pullbackOver T.hom pX
      T.right.isSheaf T.right.representableDiagonal
    let qX : Q ⟶ T.left := ReasLibPullback.pullbackOverFst T.hom pX
      T.right.isSheaf T.right.representableDiagonal
    let i : Q ⟶ P := ReasLibPullback.pullbackOverSnd T.hom pX
      T.right.isSheaf T.right.representableDiagonal
    have hq : IsPullback qX i T.hom pX := ReasLibPullback.isPullback T.hom pX
    have hp' : IsPullback (C := (CategoryTheory.Over S)ᵒᵖ ⥤ Type u)
        (pX : P.functorOfPoints ⟶ T.right.functorOfPoints) pZ g.right a :=
      IsPullback.of_hasPullback (C := (CategoryTheory.Over S)ᵒᵖ ⥤ Type u) g.right a
    have hqp : IsPullback (C := (CategoryTheory.Over S)ᵒᵖ ⥤ Type u)
        (qX : Q.functorOfPoints ⟶ T.left.functorOfPoints)
        (i ≫ pZ) (T.hom ≫ g.right) a :=
      (IsPullback.of_hasPullback (C := (CategoryTheory.Over S)ᵒᵖ ⥤ Type u) T.hom pX).paste_vert
        hp'
    obtain ⟨W₀, s₀, t₀, h₀⟩ := hc a
    let e₀ : Q.functorOfPoints ≅ yoneda.obj W₀ :=
      hqp.isoPullback ≪≫ h₀.isoPullback.symm
    haveI : IsScheme Q := IsScheme.of (X := Q)
      { hom := e₀.hom, inv := e₀.inv,
        hom_inv_id := e₀.hom_inv_id, inv_hom_id := e₀.inv_hom_id }
    haveI : IsClosedImmersion i := IsClosedImmersion.of_isPullback hq.flip
    haveI : Surjective i := Surjective.of_isPullback hq inferInstance
    haveI : IsScheme P := IsScheme.of_thickening i
    obtain ⟨W, ⟨e⟩⟩ := IsScheme.exists_scheme (X := P)
    let e' : P.functorOfPoints ≅ yoneda.obj W :=
      { hom := e.hom, inv := e.inv,
        hom_inv_id := e.hom_inv_id, inv_hom_id := e.inv_hom_id }
    refine ⟨W, yoneda.preimage (e'.inv ≫ pZ), e'.inv ≫ pX, ?_⟩
    rw [Functor.map_preimage]
    exact hp'.of_iso
      e' (Iso.refl _) (Iso.refl _) (Iso.refl _)
      (by simp) (by simp) (by simp) (by simp)
  · intro h
    apply relativelyRepresentable_of_comp g.left U.hom
    exact hw'.symm ▸ MorphismProperty.comp_mem yoneda.relativelyRepresentable
      T.hom g.right (IsClosedImmersion.presheaf (f := T.hom)).rep h

end AlgebraicGeometry.AlgebraicSpace.Thickening.Hom
