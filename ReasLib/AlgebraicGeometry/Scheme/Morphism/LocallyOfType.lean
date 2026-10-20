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
          P (CommRingCat.Hom.hom (f.appLE V U e)) := sorry

/-- `LocallyOfType` is equivalent to its pointwise affine-neighborhood witness condition. -/
@[stacks 01SS]
theorem locallyOfType_iff
    (P : {R S : Type u} → [CommRing R] → [CommRing S] → (R →+* S) → Prop)
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    LocallyOfType P f ↔
      ∀ x : X, ∃ U : X.affineOpens, x ∈ (U : X.Opens) ∧
        ∃ V : Y.affineOpens,
          ∃ e : U ≤ f ⁻¹ᵁ V,
            P (CommRingCat.Hom.hom (f.appLE V U e)) := sorry

/-- When `P` is local for ring homomorphisms, the pointwise affine-neighborhood formulation
agrees with mathlib's canonical `affineLocally P f`. -/
@[stacks 01SS]
theorem locallyOfType_iff_affineLocally
    (P : {R S : Type u} → [CommRing R] → [CommRing S] → (R →+* S) → Prop)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hP : RingHom.PropertyIsLocal P) :
    LocallyOfType P f ↔ affineLocally P f := sorry

namespace LocallyOfType

/-- If a morphism is locally of type `P` and `P` is local, then the map on sections over
compatible affine opens has property `P`. -/
theorem appLE
    (P : {R T : Type u} → [CommRing R] → [CommRing T] → (R →+* T) → Prop)
    {X S : Scheme.{u}} {f : X ⟶ S} (hf : LocallyOfType P f)
    (hP : RingHom.PropertyIsLocal P) (U : X.affineOpens) (V : S.affineOpens)
    (e : U ≤ f ⁻¹ᵁ V) :
    P (CommRingCat.Hom.hom (f.appLE V U e)) := by
  rw [locallyOfType_iff_affineLocally P f hP] at hf
  exact (affineLocally_iff_affineOpens_le P f).mp hf V U e

/-- If a morphism is locally of type `P` and `P` is local, then compatible affine opens
induce a map on sections with property `P`. -/
theorem appLE_of_isAffineOpen
    (P : {R T : Type u} → [CommRing R] → [CommRing T] → (R →+* T) → Prop)
    {X S : Scheme.{u}} {f : X ⟶ S} (hf : LocallyOfType P f)
    (hP : RingHom.PropertyIsLocal P) {U : X.Opens} (hU : IsAffineOpen U)
    {V : S.Opens} (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V) :
    P (CommRingCat.Hom.hom (f.appLE V U e)) := by
  simpa using appLE P hf hP ⟨U, hU⟩ ⟨V, hV⟩ e

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
  rw [locallyOfType_iff_affineLocally P f hP] at hf
  rw [locallyOfType_iff_affineLocally P g hP] at hg
  rw [locallyOfType_iff_affineLocally P (f ≫ g) hP]
  have hstable : (affineLocally P).IsStableUnderComposition :=
    @HasRingHomProperty.stableUnderComposition (affineLocally P) P
      (HasRingHomProperty.mk hP rfl) hcomp
  exact hstable.comp_mem f g hf hg

/-- Base change preserves the property of being locally of type `P` when `P` is local and
stable under base change. -/
theorem locallyOfType_pullback_snd
    {S' : Scheme.{u}} (hP : RingHom.PropertyIsLocal P)
    (hbc : RingHom.IsStableUnderBaseChange P)
    (hf : LocallyOfType P f) (g : S' ⟶ S) :
    LocallyOfType P (pullback.snd f g) := by
  rw [locallyOfType_iff_affineLocally P f hP] at hf
  have hstable : (affineLocally P).IsStableUnderBaseChange :=
    @HasRingHomProperty.isStableUnderBaseChange (affineLocally P) P
      (HasRingHomProperty.mk hP rfl) hbc
  exact (locallyOfType_iff_affineLocally P (pullback.snd f g) hP).2 <|
    hstable.of_isPullback (IsPullback.of_hasPullback f g) hf

/-- A scheme morphism is locally of type `P` if and only if every map on sections induced by
compatible affine opens has property `P`. -/
@[stacks 01SU]
theorem locallyOfType_iff_forall_affineOpen_appLE
    (hP : RingHom.PropertyIsLocal P) :
    LocallyOfType P f ↔
      ∀ {V : S.Opens}, IsAffineOpen V →
        ∀ {U : X.Opens}, IsAffineOpen U → ∀ e : U ≤ f ⁻¹ᵁ V,
          P (f.appLE V U e).hom := by
  rw [locallyOfType_iff_affineLocally P f hP, affineLocally_iff_forall_isAffineOpen]

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
`P`. -/
@[stacks 01SU]
theorem locallyOfType_iff_exists_affineOpenCover
    (hP : RingHom.PropertyIsLocal P) :
    LocallyOfType P f ↔
      ∃ 𝒱 : S.AffineOpenCover,
        ∀ j : 𝒱.I₀,
          ∃ 𝒰 : ((𝒱.openCover.pullback₁ f).X j).AffineOpenCover,
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
