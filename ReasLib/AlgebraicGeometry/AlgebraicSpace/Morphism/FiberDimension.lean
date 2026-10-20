module

public import Mathlib.RingTheory.KrullDimension.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Fiber.Stalk
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeDimension

/-!
# Fibre dimensions of morphisms of algebraic spaces

The relative dimension of a morphism of algebraic spaces at a point, and the
dimension of the local ring of its fibre at that point, are étale-local
numeric invariants. They are computed on any étale scheme square through the
point, matching `Scheme.Hom.fiberDimensionAt` and
`ringKrullDim (Scheme.Hom.fiberStalkAt · ·)`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The relative dimension of a morphism `f : X ⟶ Y` of algebraic spaces at a
point `x` of `X`, as the supremum of scheme-level local fibre dimensions along
étale scheme squares through `x`. -/
noncomputable def fiberDimensionAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) : WithBot ℕ∞ :=
  ⨆ (U : Over S) (V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
    (u : U.left) (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (hx : Points.mapOfOver a u = x),
    Scheme.Hom.fiberDimensionAt h.left u

/-- The dimension of the local ring of the fibre of a morphism `f : X ⟶ Y` of
algebraic spaces at a point `x` of `X`, as the supremum of Krull dimensions of
distinguished fibre stalks along étale scheme squares through `x`. -/
noncomputable def fiberStalkDimAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) : WithBot ℕ∞ :=
  ⨆ (U : Over S) (V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
    (u : U.left) (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (hx : Points.mapOfOver a u = x),
    ringKrullDim (Scheme.Hom.fiberStalkAt h.left u)

/-- The relative dimension of `f` at `x` equals the scheme-level local fibre
dimension of the top arrow of any étale scheme square through `x`. -/
theorem fiberDimensionAt_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {U V : Over S} (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (u : U.left) {x : Points X}
    (hx : Points.mapOfOver a u = x) :
    fiberDimensionAt f x = Scheme.Hom.fiberDimensionAt h.left u :=
  sorry

/-- The dimension of the local ring of the fibre of `f` at `x` equals the
Krull dimension of the distinguished fibre stalk of the top arrow of any étale
scheme square through `x`. -/
theorem fiberStalkDimAt_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {U V : Over S} (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (u : U.left) {x : Points X}
    (hx : Points.mapOfOver a u = x) :
    fiberStalkDimAt f x = ringKrullDim (Scheme.Hom.fiberStalkAt h.left u) :=
  sorry

/-- On a morphism of schemes over `S`, viewed as a morphism of algebraic spaces,
the relative dimension at a point recovers the scheme-level local fibre
dimension. -/
theorem fiberDimensionAt_ofOverMap {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) (u : U.left) :
    fiberDimensionAt (ofOverMap h) (ofOver.pointsEquiv U u) =
      Scheme.Hom.fiberDimensionAt h.left u :=
  sorry

/-- On a morphism of schemes over `S`, viewed as a morphism of algebraic spaces,
the dimension of the local ring of the fibre recovers the Krull dimension of
the distinguished fibre stalk. -/
theorem fiberStalkDimAt_ofOverMap {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) (u : U.left) :
    fiberStalkDimAt (ofOverMap h) (ofOver.pointsEquiv U u) =
      ringKrullDim (Scheme.Hom.fiberStalkAt h.left u) :=
  sorry

/-- Exact relative dimension `d` at a point is the numeric relative dimension
taking the value `d`. -/
theorem relativeDimensionAt_iff_fiberDimensionAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (d : ℕ) (x : Points X) :
    RelativeDimensionAt f d x ↔ fiberDimensionAt f x = (d : WithBot ℕ∞) :=
  sorry

/-- Relative dimension at most `d` at a point is the numeric relative dimension
being at most `d`. -/
theorem relativeDimensionLEAt_iff_fiberDimensionAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) (d : ℕ) (x : Points X) :
    RelativeDimensionLEAt f d x ↔ fiberDimensionAt f x ≤ (d : WithBot ℕ∞) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
