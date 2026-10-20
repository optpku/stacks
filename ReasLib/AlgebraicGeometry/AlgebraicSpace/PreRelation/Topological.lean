/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

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
      Points.map P.s.left ⁻¹' T = Points.map P.t.left ⁻¹' T := sorry

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
        IsClosed Z → IsPointsInvariant P Z → IsClosed (Points.map φ.left '' Z) := sorry

/-- A closed invariant subset of the points of `U` has closed image in the points of `X`. -/
theorem mapsInvariantClosed_spec {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    {P : PreRelation U} {φ : U ⟶ X} (h : MapsInvariantClosed P φ)
    {Z : Set (Points U.left)} (hZ : IsClosed Z) (hinv : IsPointsInvariant P Z) :
    IsClosed (Points.map φ.left '' Z) := sorry

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
              Points.map φ.left '' Z₁ ∩ Points.map φ.left '' Z₂ := sorry

/-- The two defining conditions of `IntersectInvariantClosed`. -/
theorem intersectInvariantClosed_spec {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    {P : PreRelation U} {φ : U ⟶ X} (h : IntersectInvariantClosed P φ) :
    (∀ {Z : Set (Points U.left)},
        IsClosed Z → IsPointsInvariant P Z → IsClosed (Points.map φ.left '' Z)) ∧
      ∀ {Z₁ Z₂ : Set (Points U.left)},
        IsClosed Z₁ → IsPointsInvariant P Z₁ →
        IsClosed Z₂ → IsPointsInvariant P Z₂ →
          Points.map φ.left '' (Z₁ ∩ Z₂) =
            Points.map φ.left '' Z₁ ∩ Points.map φ.left '' Z₂ := sorry

/-- Preservation of invariant closed-set intersections includes closedness of
invariant closed images. -/
theorem IntersectInvariantClosed.toMapsInvariantClosed {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} {P : PreRelation U} {φ : U ⟶ X} (h : IntersectInvariantClosed P φ) :
    MapsInvariantClosed P φ := sorry

/-- The morphism from the relation to the kernel pair of an invariant morphism is
universally submersive. -/
def inducedUniversallySubmersive {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) : Prop :=
  UniversallySubmersive (P.induced hφ).left

/-- Universal submersiveness of the induced kernel-pair morphism is universal
submersiveness of its underlying algebraic-space morphism. -/
theorem inducedUniversallySubmersive_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) :
    inducedUniversallySubmersive P hφ ↔ UniversallySubmersive (P.induced hφ).left := sorry

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
        Q (P.baseChange hφ f) (pullback.snd φ f) (P.isInvariantHom_pullback_snd hφ f) := sorry

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
        Q (P.baseChange hφ f) (pullback.snd φ f) (P.isInvariantHom_pullback_snd hφ f) := sorry

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
        IntersectInvariantClosed (P.baseChange hφ g) (pullback.snd φ g) := sorry

/-- Universal preservation of invariant closed-set intersections is universal
holding of `IntersectInvariantClosed`. -/
theorem universallyIntersectInvariantClosed_iff_holdsUniversally
    {S : Scheme.{u}} {B : AlgebraicSpace S} {U X : Over B}
    (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) :
    UniversallyIntersectInvariantClosed P φ hφ ↔
      holdsUniversally P hφ fun P' φ' _ ↦ IntersectInvariantClosed P' φ' := sorry

/-- Universal holding of submersiveness in `Over B` is equivalent to universal
submersiveness of the underlying algebraic-space morphism. -/
theorem holdsUniversally_submersive_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) {φ : U ⟶ X} (hφ : P.IsInvariantHom φ) :
    holdsUniversally P hφ (fun _ φ' _ ↦ Submersive φ'.left) ↔ UniversallySubmersive φ.left := sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
