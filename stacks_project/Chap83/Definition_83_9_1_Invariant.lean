module

public import stacks_project.Chap66.Lemma_66_4_6_Topology
public import stacks_project.Chap83.Definition_83_4_4_Quotient

/-!
# Invariant closed sets and universal condition (3)

A subset of the points of `U` is invariant for a pre-relation when its preimages along the two
projections agree. Condition (3) asks that closed invariant subsets have closed images and that
binary intersections of such sets are preserved; a good quotient requires this after every base
change of the quotient morphism.
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
  sorry

/-- Condition (3): closed invariant subsets of the points of `U` have closed images, and the
morphism preserves binary intersections of such subsets. -/
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

/-- Condition (3) is closedness of images of closed invariant subsets together with preservation
of their binary intersections. -/
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
  sorry

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
  sorry

/-- Condition (3) holds universally: for an `R`-invariant morphism `φ`, after every base
change `g : X' ⟶ X` in `Over B`, the source base change `R' = X' ×_X R` still satisfies
`IntersectInvariantClosed` for `U' ⟶ X'`. -/
def UniversallyIntersectInvariantClosed {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) (φ : U ⟶ X) (hφ : P.IsInvariantHom φ) : Prop :=
  ∀ {X' : Over B} (g : X' ⟶ X),
    IntersectInvariantClosed (P.baseChange hφ g) (pullback.snd φ g)

/-- Universal condition (3) is `IntersectInvariantClosed` for `P.baseChange hφ g` and
`pullback.snd φ g` after every base change in `Over B`. -/
theorem universallyIntersectInvariantClosed_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    {U X : Over B} (P : PreRelation U) (φ : U ⟶ X) (hφ : P.IsInvariantHom φ) :
    UniversallyIntersectInvariantClosed P φ hφ ↔
      ∀ {X' : Over B} (g : X' ⟶ X),
        IntersectInvariantClosed (P.baseChange hφ g) (pullback.snd φ g) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.PreRelation
