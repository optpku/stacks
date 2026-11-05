/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties

/-!
# Scheme morphisms locally satisfying a ring-map property

This file provides the pointwise affine-neighborhood formulation of a property of scheme
morphisms. It is independent of any particular property of ring homomorphisms, so
specializations such as finite type, finite presentation, syntomicity, and finite locally free
morphisms can share one owner.
-/

@[expose] public section

open AlgebraicGeometry
open TopologicalSpace
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A scheme morphism `f : X ⟶ Y` is locally of type `P` when every point of `X` lies in an
affine open `U` mapping into an affine open `V` of `Y`, with `Γ(Y, V) ⟶ Γ(X, U)` satisfying
`P`. -/
@[stacks 01SS]
class LocallyOfType
    (P : {R S : Type u} → [CommRing R] → [CommRing S] → (R →+* S) → Prop)
    {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  property :
    ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
      ∃ V : Y.affineOpens,
        ∃ e : U ≤ f ⁻¹ᵁ V,
          P (CommRingCat.Hom.hom (f.appLE V U e))

/-- A `LocallyOfType` hypothesis supplies the affine-neighborhood witness at each point. -/
@[stacks 01SS]
theorem LocallyOfType.exists_affineNeighborhood
    (P : {R S : Type u} → [CommRing R] → [CommRing S] → (R →+* S) → Prop)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (hf : LocallyOfType P f) (x : X) :
    ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
      ∃ V : Y.affineOpens,
        ∃ e : U ≤ f ⁻¹ᵁ V,
          P (CommRingCat.Hom.hom (f.appLE V U e)) := hf.property x

/-- `LocallyOfType` is equivalent to its pointwise affine-neighborhood witness condition. -/
@[stacks 01SS]
theorem locallyOfType_iff
    (P : {R S : Type u} → [CommRing R] → [CommRing S] → (R →+* S) → Prop)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    LocallyOfType P f ↔
      ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        ∃ V : Y.affineOpens,
          ∃ e : U ≤ f ⁻¹ᵁ V,
            P (CommRingCat.Hom.hom (f.appLE V U e)) := ⟨fun hf ↦ hf.property, fun hf ↦ ⟨hf⟩⟩

/-- When `P` is local for ring homomorphisms and stable under composition with source
localizations, the pointwise affine-neighborhood formulation agrees with mathlib's canonical
`affineLocally P f`. -/
@[stacks 01SS]
theorem locallyOfType_iff_affineLocally
    (P : {R S : Type u} → [CommRing R] → [CommRing S] → (R →+* S) → Prop)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hP : RingHom.PropertyIsLocal P)
    (hsource : RingHom.StableUnderCompositionWithLocalizationAwaySource P) :
    LocallyOfType P f ↔ affineLocally P f := by
  letI : HasRingHomProperty (affineLocally P) P := ⟨hP, rfl⟩
  rw [HasRingHomProperty.iff_exists_appLE (P := affineLocally P) hsource]
  rw [locallyOfType_iff]
  exact forall_congr' fun x ↦ by
    constructor
    · rintro ⟨U, hx, V, e, h⟩
      exact ⟨V, U, hx, e, h⟩
    · rintro ⟨V, U, hx, e, h⟩
      exact ⟨U, hx, V, e, h⟩

namespace LocallyOfType

/-- Under full locality, including source-localization stability, a morphism locally of type
`P` induces section-ring maps with property `P` on all compatible affine opens. -/
theorem appLE
    (P : {R T : Type u} → [CommRing R] → [CommRing T] → (R →+* T) → Prop)
    {X S : Scheme.{u}} {f : X ⟶ S} (hf : LocallyOfType P f)
    (hP : RingHom.PropertyIsLocal P)
    (hsource : RingHom.StableUnderCompositionWithLocalizationAwaySource P)
    (U : X.affineOpens) (V : S.affineOpens)
    (e : U ≤ f ⁻¹ᵁ V) :
    P (CommRingCat.Hom.hom (f.appLE V U e)) := by
  rw [locallyOfType_iff_affineLocally P f hP hsource] at hf
  exact (affineLocally_iff_affineOpens_le P f).mp hf V U e

/-- Under full locality, including source-localization stability, compatible affine opens
induce a map on sections with property `P`. -/
theorem appLE_of_isAffineOpen
    (P : {R T : Type u} → [CommRing R] → [CommRing T] → (R →+* T) → Prop)
    {X S : Scheme.{u}} {f : X ⟶ S} (hf : LocallyOfType P f)
    (hP : RingHom.PropertyIsLocal P)
    (hsource : RingHom.StableUnderCompositionWithLocalizationAwaySource P)
    {U : X.Opens} (hU : IsAffineOpen U)
    {V : S.Opens} (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V) :
    P (CommRingCat.Hom.hom (f.appLE V U e)) := by
  simpa using appLE P hf hP hsource ⟨U, hU⟩ ⟨V, hV⟩ e

end LocallyOfType

variable {X S : Scheme.{u}} {f : X ⟶ S}
variable
  (P : {R T : Type u} → [CommRing R] → [CommRing T] → (R →+* T) → Prop)

/-- The composite of two scheme morphisms locally of type `P` is locally of type `P` when
`P` is local and stable under composition. -/
theorem locallyOfType_comp
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hP : RingHom.PropertyIsLocal P) (hcomp : RingHom.StableUnderComposition P)
    (hf : LocallyOfType P f) (hg : LocallyOfType P g) :
    LocallyOfType P (f ≫ g) := by
  refine ⟨fun x ↦ ?_⟩
  obtain ⟨U, hx, V, e, hfU⟩ := hf.property x
  obtain ⟨Vg, hfx, W, eg, hgV⟩ := hg.property (f x)
  obtain ⟨r, s, hxs, es, hfs⟩ := exists_basicOpen_le_appLE_of_appLE_of_isAffine (P := P)
    hP.StableUnderCompositionWithLocalizationAwayTarget hP.localizationAwayPreserves
    x Vg V U U hx hx e hfU hfx
  have hr : Y.basicOpen r ≤ g ⁻¹ᵁ W := (Y.basicOpen_le r).trans eg
  have hg' : P (g.appLE W (Y.basicOpen r) hr).hom := by
    haveI := Vg.2.isLocalization_basicOpen r
    rw [← g.appLE_map eg (homOfLE (Y.basicOpen_le r)).op]
    exact hP.StableUnderCompositionWithLocalizationAwayTarget _ r _ hgV
  refine ⟨⟨X.basicOpen s, U.2.basicOpen s⟩, hxs, W,
    es.trans (f.preimage_mono hr), ?_⟩
  rw [← Scheme.Hom.appLE_comp_appLE f g W (Y.basicOpen r) (X.basicOpen s) hr es,
    CommRingCat.hom_comp]
  exact hcomp _ _ hg' hfs

/-- Base change preserves the property of being locally of type `P` when `P` is local and
stable under base change. -/
theorem locallyOfType_pullback_snd
    {S' : Scheme.{u}} (hP : RingHom.PropertyIsLocal P)
    (hbc : RingHom.IsStableUnderBaseChange P)
    (hf : LocallyOfType P f) (g : S' ⟶ S) :
    LocallyOfType P (pullback.snd f g) := by
  letI : HasRingHomProperty (affineLocally P) P := ⟨hP, rfl⟩
  have hstable : (affineLocally P).IsStableUnderBaseChange :=
    HasRingHomProperty.isStableUnderBaseChange hbc
  refine ⟨fun z ↦ ?_⟩
  obtain ⟨U, hx, V, e, hfU⟩ := hf.property (pullback.fst f g z)
  have hy : pullback.snd f g z ∈ g ⁻¹ᵁ (V : S.Opens) := by
    change g (pullback.snd f g z) ∈ (V : S.Opens)
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]
    exact e hx
  obtain ⟨(W : S'.Opens), hW, hyW, d⟩ :=
    Opens.isBasis_iff_nbhd.mp S'.isBasis_affineOpens hy
  letI : IsAffine W.toScheme := hW
  let O : (pullback f g).Opens := pullback.snd f g ⁻¹ᵁ W ⊓ pullback.fst f g ⁻¹ᵁ U
  have hz : z ∈ O := ⟨hyW, hx⟩
  have hf' : affineLocally P (f.resLE V U e) := by
    apply (HasRingHomProperty.iff_of_isAffine (P := affineLocally P)).mpr
    exact (hP.respectsIso.arrow_mk_iso_iff (arrowResLEAppIso f V U e)).mpr hfU
  have hsq := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback f g).flip
    e d (show O = pullback.snd f g ⁻¹ᵁ W ⊓ pullback.fst f g ⁻¹ᵁ U from rfl)
  have hlocal : affineLocally P ((pullback.snd f g).resLE W O inf_le_left) :=
    hstable.of_isPullback hsq.flip hf'
  obtain ⟨Q, hQ, hzQ, _⟩ := Opens.isBasis_iff_nbhd.mp O.toScheme.isBasis_affineOpens
    (show (⟨z, hz⟩ : O.toScheme) ∈ (⊤ : O.toScheme.Opens) from trivial)
  have hQle : Q ≤ (pullback.snd f g).resLE W O inf_le_left ⁻¹ᵁ ⊤ := by simp
  have happ := HasRingHomProperty.appLE (affineLocally P)
    ((pullback.snd f g).resLE W O inf_le_left) hlocal
    ⟨⊤, isAffineOpen_top _⟩ ⟨Q, hQ⟩ hQle
  rw [Scheme.Hom.resLE_appLE] at happ
  exact ⟨⟨O.ι ''ᵁ Q, hQ.image_of_isOpenImmersion O.ι⟩,
    ⟨⟨z, hz⟩, hzQ, rfl⟩,
    ⟨W.ι ''ᵁ ⊤, (isAffineOpen_top _).image_of_isOpenImmersion W.ι⟩,
    (Scheme.Hom.le_resLE_preimage_iff _ _ _ _).mp hQle, happ⟩

/-- A scheme morphism is locally of type `P` if and only if every map on sections induced by
compatible affine opens has property `P`, assuming full locality (including source-localization
stability). -/
@[stacks 01SU]
theorem locallyOfType_iff_forall_affineOpen_appLE
    (hP : RingHom.PropertyIsLocal P)
    (hsource : RingHom.StableUnderCompositionWithLocalizationAwaySource P) :
    LocallyOfType P f ↔
      ∀ {V : S.Opens}, IsAffineOpen V →
        ∀ {U : X.Opens}, IsAffineOpen U → ∀ e : U ≤ f ⁻¹ᵁ V,
          P (f.appLE V U e).hom := by
  rw [locallyOfType_iff_affineLocally P f hP hsource, affineLocally_iff_forall_isAffineOpen]

/-- A scheme morphism is locally of type `P` if and only if the target has an open cover whose
pullbacks have open covers by morphisms locally of type `P`. -/
@[stacks 01SU]
theorem locallyOfType_iff_exists_openCover
    (hP : RingHom.PropertyIsLocal P) :
    LocallyOfType P f ↔
      ∃ 𝒱 : S.OpenCover,
        ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.pullback₁ f).X j).OpenCover,
            ∀ i : 𝒰.I₀, LocallyOfType P (𝒰.f i ≫ 𝒱.pullbackHom f j) := sorry

/-- A scheme morphism is locally of type `P` if and only if the target has an affine open cover
whose pullbacks have affine open covers with all induced maps on global sections satisfying
`P`, assuming full locality (including source-localization stability). -/
@[stacks 01SU]
theorem locallyOfType_iff_exists_affineOpenCover
    (hP : RingHom.PropertyIsLocal P)
    (hsource : RingHom.StableUnderCompositionWithLocalizationAwaySource P) :
    LocallyOfType P f ↔
      ∃ 𝒱 : S.AffineOpenCover.{u},
        ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover.{u},
            ∀ i : 𝒰.I₀,
              P ((𝒰.f i ≫ 𝒱.openCover.pullbackHom f j).appTop).hom := sorry

/-- Restricting a morphism locally of type `P` to compatible open subschemes preserves the
property of being locally of type `P`. -/
@[stacks 01SU]
theorem locallyOfType_resLE
    (hP : RingHom.PropertyIsLocal P)
    (hf : LocallyOfType P f) {V : S.Opens} {U : X.Opens} (e : U ≤ f ⁻¹ᵁ V) :
    LocallyOfType P (f.resLE V U e) := sorry

end AlgebraicGeometry
