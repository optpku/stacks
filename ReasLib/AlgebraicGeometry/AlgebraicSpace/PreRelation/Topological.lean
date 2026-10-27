/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Maps.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Submersive
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.QuotientSheaf.BaseChange
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.PreRelation.Comparison

/-!
# Topological properties of invariant morphisms

Closed invariant subsets, their intersections, and the induced kernel-pair morphism
provide topological predicates, with flat and arbitrary base-change variants.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.PreRelation

/-- A subset of the points of `U` is invariant for a pre-relation `P` when its preimages along
`P.s` and `P.t` agree. -/
def IsPointsInvariant {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) (T : Set (Points U.left)) : Prop :=
  Points.map P.s.left ⁻¹' T = Points.map P.t.left ⁻¹' T

/-- Set-theoretic invariance is equality of the two projection preimages. -/
theorem isPointsInvariant_iff {S : Scheme.{u}} {B : AlgebraicSpace S} {U : Over B}
    (P : PreRelation U) (T : Set (Points U.left)) :
    IsPointsInvariant P T ↔
      Points.map P.s.left ⁻¹' T = Points.map P.t.left ⁻¹' T :=
  Iff.rfl

/-- A morphism maps closed invariant subsets of its source point space to closed
subsets of its target point space. -/
def MapsInvariantClosed {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) : Prop :=
  ∀ {Z : Set (Points U.left)},
    IsClosed Z → IsPointsInvariant P Z → IsClosed (Points.map φ.left '' Z)

/-- Mapping invariant closed sets to closed sets is equivalent to closedness of each
such image. -/
theorem mapsInvariantClosed_iff {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) :
    MapsInvariantClosed P φ ↔
      ∀ {Z : Set (Points U.left)},
        IsClosed Z → IsPointsInvariant P Z → IsClosed (Points.map φ.left '' Z) :=
  Iff.rfl

/-- A closed invariant subset of the points of `U` has closed image in the points of `X`. -/
theorem mapsInvariantClosed_spec {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    {P : PreRelation U} {φ : U ⟶ X} (h : MapsInvariantClosed P φ)
    {Z : Set (Points U.left)} (hZ : IsClosed Z) (hinv : IsPointsInvariant P Z) :
    IsClosed (Points.map φ.left '' Z) :=
  h hZ hinv

/-- A morphism has closed images of invariant closed subsets and preserves their
binary intersections. -/
structure IntersectInvariantClosed {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) : Prop where
  /-- The image of a closed invariant subset is closed. -/
  image_isClosed : ∀ {Z : Set (Points U.left)},
    IsClosed Z → IsPointsInvariant P Z → IsClosed (Points.map φ.left '' Z)
  /-- Binary intersections of closed invariant subsets are preserved. -/
  map_inter : ∀ {Z₁ Z₂ : Set (Points U.left)},
    IsClosed Z₁ → IsPointsInvariant P Z₁ →
    IsClosed Z₂ → IsPointsInvariant P Z₂ →
      Points.map φ.left '' (Z₁ ∩ Z₂) =
        Points.map φ.left '' Z₁ ∩ Points.map φ.left '' Z₂

/-- Build an `IntersectInvariantClosed` witness from closedness of images and preservation of
binary intersections. -/
def IntersectInvariantClosed.of {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    {P : PreRelation U} {φ : U ⟶ X}
    (h_closed : ∀ {Z : Set (Points U.left)},
      IsClosed Z → IsPointsInvariant P Z → IsClosed (Points.map φ.left '' Z))
    (h_inter : ∀ {Z₁ Z₂ : Set (Points U.left)},
      IsClosed Z₁ → IsPointsInvariant P Z₁ →
      IsClosed Z₂ → IsPointsInvariant P Z₂ →
        Points.map φ.left '' (Z₁ ∩ Z₂) =
          Points.map φ.left '' Z₁ ∩ Points.map φ.left '' Z₂) :
    IntersectInvariantClosed P φ where
  image_isClosed := h_closed
  map_inter := h_inter

/-- The invariant closed-set intersection property is equivalent to closedness of
images together with preservation of binary intersections. -/
theorem intersectInvariantClosed_iff {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) (φ : U ⟶ X) :
    IntersectInvariantClosed P φ ↔
      (∀ {Z : Set (Points U.left)},
          IsClosed Z → IsPointsInvariant P Z → IsClosed (Points.map φ.left '' Z)) ∧
        ∀ {Z₁ Z₂ : Set (Points U.left)},
          IsClosed Z₁ → IsPointsInvariant P Z₁ →
          IsClosed Z₂ → IsPointsInvariant P Z₂ →
            Points.map φ.left '' (Z₁ ∩ Z₂) =
              Points.map φ.left '' Z₁ ∩ Points.map φ.left '' Z₂ :=
  ⟨fun h ↦ ⟨h.image_isClosed, h.map_inter⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- The two defining conditions of `IntersectInvariantClosed`. -/
theorem intersectInvariantClosed_spec {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    {P : PreRelation U} {φ : U ⟶ X} (h : IntersectInvariantClosed P φ) :
    (∀ {Z : Set (Points U.left)},
        IsClosed Z → IsPointsInvariant P Z → IsClosed (Points.map φ.left '' Z)) ∧
      ∀ {Z₁ Z₂ : Set (Points U.left)},
        IsClosed Z₁ → IsPointsInvariant P Z₁ →
        IsClosed Z₂ → IsPointsInvariant P Z₂ →
          Points.map φ.left '' (Z₁ ∩ Z₂) =
            Points.map φ.left '' Z₁ ∩ Points.map φ.left '' Z₂ :=
  ⟨h.image_isClosed, h.map_inter⟩

/-- Preservation of invariant closed-set intersections includes closedness of
invariant closed images. -/
theorem IntersectInvariantClosed.toMapsInvariantClosed {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} {P : PreRelation U} {φ : U ⟶ X} (h : IntersectInvariantClosed P φ) :
    MapsInvariantClosed P φ :=
  h.image_isClosed

/-- The morphism from the relation to the kernel pair of an invariant morphism is
universally submersive. -/
def inducedUniversallySubmersive {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) : Prop :=
  UniversallySubmersive (P.induced hφ).left

/-- Universal submersiveness of the induced kernel-pair morphism is universal
submersiveness of its underlying algebraic-space morphism. -/
theorem inducedUniversallySubmersive_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) :
    inducedUniversallySubmersive P hφ ↔ UniversallySubmersive (P.induced hφ).left :=
  Iff.rfl

/-- A predicate on invariant morphisms holds uniformly when it holds after every
flat base change in `Over B`. -/
def holdsUniformly {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (Q : ∀ {U' X' : Over B} (P' : PreRelation U') (φ' : U' ⟶ X'),
      P'.IsInvariantHom φ' → Prop) : Prop :=
  ∀ {X' : Over B} (f : X' ⟶ X), Flat f.left →
    Q (P.baseChange hφ f) (pullback.snd φ f) (P.isInvariantHom_pullback_snd hφ f)

/-- Uniform holding is equivalent to the predicate holding after every flat base
change in `Over B`. -/
theorem holdsUniformly_iff {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (Q : ∀ {U' X' : Over B} (P' : PreRelation U') (φ' : U' ⟶ X'),
      P'.IsInvariantHom φ' → Prop) :
    holdsUniformly P hφ Q ↔
      ∀ {X' : Over B} (f : X' ⟶ X), Flat f.left →
        Q (P.baseChange hφ f) (pullback.snd φ f) (P.isInvariantHom_pullback_snd hφ f) :=
  Iff.rfl

/-- A predicate on invariant morphisms holds universally when it holds after every
base change in `Over B`. -/
def holdsUniversally {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (Q : ∀ {U' X' : Over B} (P' : PreRelation U') (φ' : U' ⟶ X'),
      P'.IsInvariantHom φ' → Prop) : Prop :=
  ∀ {X' : Over B} (f : X' ⟶ X),
    Q (P.baseChange hφ f) (pullback.snd φ f) (P.isInvariantHom_pullback_snd hφ f)

/-- Universal holding is equivalent to the predicate holding after every base
change in `Over B`. -/
theorem holdsUniversally_iff {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ)
    (Q : ∀ {U' X' : Over B} (P' : PreRelation U') (φ' : U' ⟶ X'),
      P'.IsInvariantHom φ' → Prop) :
    holdsUniversally P hφ Q ↔
      ∀ {X' : Over B} (f : X' ⟶ X),
        Q (P.baseChange hφ f) (pullback.snd φ f) (P.isInvariantHom_pullback_snd hφ f) :=
  Iff.rfl

/-- Every base change has closed images of invariant closed subsets and preserves
their binary intersections. -/
def UniversallyIntersectInvariantClosed {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) (φ : U ⟶ X) (hφ : P.IsInvariantHom φ) : Prop :=
  ∀ {X' : Over B} (g : X' ⟶ X),
    IntersectInvariantClosed (P.baseChange hφ g) (pullback.snd φ g)

/-- The universal invariant closed-set intersection property is equivalent to
its holding after every base change in `Over B`. -/
theorem universallyIntersectInvariantClosed_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) (φ : U ⟶ X) (hφ : P.IsInvariantHom φ) :
    UniversallyIntersectInvariantClosed P φ hφ ↔
      ∀ {X' : Over B} (g : X' ⟶ X),
        IntersectInvariantClosed (P.baseChange hφ g) (pullback.snd φ g) :=
  Iff.rfl

/-- Universal preservation of invariant closed-set intersections is universal
holding of `IntersectInvariantClosed`. -/
theorem universallyIntersectInvariantClosed_iff_holdsUniversally
    {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) :
    UniversallyIntersectInvariantClosed P φ hφ ↔
      holdsUniversally P hφ fun P' φ' _ ↦ IntersectInvariantClosed P' φ' :=
  Iff.rfl

private theorem pointsMap_id {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) : Points.map (𝟙 X) x = x :=
  Quotient.inductionOn x (fun _ ↦ rfl)

private theorem pointsMap_comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) (x : Points X) :
    Points.map (f ≫ g) x = Points.map g (Points.map f x) :=
  Quotient.inductionOn x (fun _ ↦ rfl)

private theorem pointsMap_iso_surjective {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (e : X ≅ Y) : Function.Surjective (Points.map e.hom) := by
  intro y
  refine ⟨Points.map e.inv y, ?_⟩
  rw [← pointsMap_comp, e.inv_hom_id, pointsMap_id]

private theorem isPointsTopology_coinduced_iso {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (e : X ≅ Y) {τX : TopologicalSpace (Points X)} (hX : IsPointsTopology X τX) :
    IsPointsTopology Y (TopologicalSpace.coinduced (Points.map e.hom) τX) := by
  intro U p hp hs
  letI : TopologicalSpace (Points X) := τX
  letI : TopologicalSpace (Points Y) := TopologicalSpace.coinduced (Points.map e.hom) τX
  letI : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S) p := hs
  let ei : Y.functorOfPoints ≅ X.functorOfPoints :=
    { hom := e.inv, inv := e.hom, hom_inv_id := e.inv_hom_id, inv_hom_id := e.hom_inv_id }
  letI : IsIso (C := (Over S)ᵒᵖ ⥤ Type u) ei.hom := ei.isIso_hom
  have hp' : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf (p ≫ ei.hom) :=
    (MorphismProperty.cancel_right_of_respectsIso
      (C := (Over S)ᵒᵖ ⥤ Type u) (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf
      (p : (ofOver U).functorOfPoints ⟶ Y.functorOfPoints) ei.hom).mpr hp
  have hs' : Presheaf.IsLocallySurjective (Scheme.etaleTopology.over S)
      ((p : (ofOver U).functorOfPoints ⟶ Y.functorOfPoints) ≫ ei.hom) := by infer_instance
  have hq := hX U (p ≫ ei.hom) hp' hs'
  have he : Topology.IsQuotientMap (Points.map e.hom) :=
    ⟨⟨rfl⟩, pointsMap_iso_surjective e⟩
  convert he.comp hq using 1
  funext x
  change Points.map p (ofOver.pointsEquiv U x) =
    Points.map e.hom (Points.map (p ≫ e.inv) (ofOver.pointsEquiv U x))
  simp only [← pointsMap_comp, Category.assoc, e.inv_hom_id,
    Category.comp_id]

private theorem submersive_comp_iso {S : Scheme.{u}} {X X' Y : AlgebraicSpace S}
    (e : X' ≅ X) {f : X ⟶ Y} (hf : Submersive f) : Submersive (e.hom ≫ f) := by
  constructor
  intro τX' τY hX' hY
  letI : TopologicalSpace (Points X') := τX'
  letI : TopologicalSpace (Points X) := TopologicalSpace.coinduced (Points.map e.hom) τX'
  letI : TopologicalSpace (Points Y) := τY
  have he : Topology.IsQuotientMap (Points.map e.hom) :=
    ⟨⟨rfl⟩, pointsMap_iso_surjective e⟩
  have hq := hf.isQuotientMap _ τY (isPointsTopology_coinduced_iso e hX') hY
  change Topology.IsQuotientMap (Points.map (e.hom ≫ f))
  convert hq.comp he using 1
  funext x
  exact pointsMap_comp _ _ x

/-- Universal holding of submersiveness in `Over B` is equivalent to universal
submersiveness of the underlying algebraic-space morphism. -/
theorem holdsUniversally_submersive_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) :
    holdsUniversally P hφ (fun _ φ' _ ↦ Submersive φ'.left) ↔ UniversallySubmersive φ.left := by
  constructor
  · intro h
    constructor
    intro V W i₁ i₂ f' hs
    let W' : Over B := Over.mk (i₂ ≫ X.hom)
    let g : W' ⟶ X := Over.homMk i₂ rfl
    have hp := ((IsPullback.of_hasPullback φ g).flip).map (Over.forget B)
    let e := hs.isoIsPullback _ _ hp
    have hsub := submersive_comp_iso e (h g)
    have he : e.hom ≫ (pullback.snd φ g).left = f' :=
      hs.isoIsPullback_hom_fst _ _ hp
    rw [← he]
    exact hsub.isQuotientMap
  · intro h X' g
    exact ⟨h.universally_isQuotientMap _ _ _
      (((IsPullback.of_hasPullback φ g).flip).map (Over.forget B))⟩

end AlgebraicGeometry.AlgebraicSpace.PreRelation
