/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.Topology.KrullDimension.Local
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Comparison
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.FiberStalkDimension
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.ResidueFieldTrdeg

/-!
# Relative dimension of morphisms of algebraic spaces

A morphism of algebraic spaces has relative dimension at most `d`, or equal to
`d`, when the local topological Krull dimension of an étale-local
scheme-theoretic fibre is bounded by, or equal to, `d` at every point of the
source.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces has relative dimension at most
`d` at a point `x` of `X` if some étale scheme square over `f` has
scheme-theoretic fibre of local topological Krull dimension at most `d` at a
point of `U` mapping to `x`. -/
def RelativeDimensionLEAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ) (x : Points X) : Prop :=
  ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
    (u : U.left),
    (over (@AlgebraicGeometry.Etale)).presheaf a ∧
      (over (@AlgebraicGeometry.Etale)).presheaf b ∧
        a ≫ f = ofOverMap h ≫ b ∧
          Points.map a (ofOver.pointsEquiv U u) = x ∧
            topologicalKrullDimAt (h.left.asFiber u) ≤ (d : WithBot ℕ∞)

/-- Relative dimension at most `d` at a point is the existence of an étale
scheme presentation whose scheme-theoretic fibre has local topological Krull
dimension at most `d` at a germ mapping to that point. -/
theorem relativeDimensionLEAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ) (x : Points X) :
    RelativeDimensionLEAt f d x ↔
      ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
        (u : U.left),
        (over (@AlgebraicGeometry.Etale)).presheaf a ∧
          (over (@AlgebraicGeometry.Etale)).presheaf b ∧
            a ≫ f = ofOverMap h ≫ b ∧
              Points.map a (ofOver.pointsEquiv U u) = x ∧
                topologicalKrullDimAt (h.left.asFiber u) ≤ (d : WithBot ℕ∞) :=
  sorry

namespace RelativeDimensionLEAt

/-- An étale scheme square over `f` whose scheme-theoretic fibre has local
topological Krull dimension at most `d` at a germ mapping to `x` witnesses the
pointwise bound at `x`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {d : ℕ}
    {x : Points X} {U V : Over S} {a : ofOver U ⟶ X} {b : ofOver V ⟶ Y}
    {h : U ⟶ V} {u : U.left}
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b)
    (hx : Points.map a (ofOver.pointsEquiv U u) = x)
    (hu : topologicalKrullDimAt (h.left.asFiber u) ≤ (d : WithBot ℕ∞)) :
    RelativeDimensionLEAt f d x :=
  sorry

end RelativeDimensionLEAt

/-- Given one étale scheme square over `f` with a germ mapping to `x`, the
pointwise bound at `x` is equivalent to the local topological Krull dimension
of the scheme-theoretic fibre being at most `d` at that germ. -/
theorem relativeDimensionLEAt_iff_of_etale {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} {d : ℕ} {x : Points X}
    {U V : Over S} {a : ofOver U ⟶ X} {b : ofOver V ⟶ Y} {h : U ⟶ V}
    {u : U.left} (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b)
    (hx : Points.map a (ofOver.pointsEquiv U u) = x) :
    RelativeDimensionLEAt f d x ↔
      topologicalKrullDimAt (h.left.asFiber u) ≤ (d : WithBot ℕ∞) :=
  sorry

/-- A morphism `f : X ⟶ Y` of algebraic spaces has relative dimension `d` at a
point `x` of `X` if some étale scheme square over `f` has scheme-theoretic fibre
of local topological Krull dimension exactly `d` at a point of `U` mapping to
`x`. -/
def RelativeDimensionEqAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ∞) (x : Points X) : Prop :=
  ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
    (u : U.left),
    (over (@AlgebraicGeometry.Etale)).presheaf a ∧
      (over (@AlgebraicGeometry.Etale)).presheaf b ∧
        a ≫ f = ofOverMap h ≫ b ∧
          Points.map a (ofOver.pointsEquiv U u) = x ∧
            topologicalKrullDimAt (h.left.asFiber u) = (d : WithBot ℕ∞)

/-- Relative dimension `d` at a point is the existence of an étale scheme
presentation whose scheme-theoretic fibre has local topological Krull dimension
`d` at a germ mapping to that point. -/
theorem relativeDimensionEqAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ∞) (x : Points X) :
    RelativeDimensionEqAt f d x ↔
      ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
        (u : U.left),
        (over (@AlgebraicGeometry.Etale)).presheaf a ∧
          (over (@AlgebraicGeometry.Etale)).presheaf b ∧
            a ≫ f = ofOverMap h ≫ b ∧
              Points.map a (ofOver.pointsEquiv U u) = x ∧
                topologicalKrullDimAt (h.left.asFiber u) = (d : WithBot ℕ∞) :=
  sorry

/-- Relative dimension `d` at `x` holds if and only if every étale scheme square
through `x` has `dim_u(U_v) = d`. -/
theorem relativeDimensionEqAt_iff_forall {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ∞) (x : Points X) :
    RelativeDimensionEqAt f d x ↔
      ∀ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
        (u : U.left),
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a →
          (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = ofOverMap h ≫ b →
              Points.mapOfOver a u = x →
                topologicalKrullDimAt (h.left.asFiber u) = (d : WithBot ℕ∞) :=
  sorry

namespace RelativeDimensionEqAt

/-- An étale scheme square over `f` whose scheme-theoretic fibre has local
topological Krull dimension `d` at a germ mapping to `x` witnesses exact
relative dimension `d` at `x`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {d : ℕ∞}
    {x : Points X} {U V : Over S} {a : ofOver U ⟶ X} {b : ofOver V ⟶ Y}
    {h : U ⟶ V} {u : U.left}
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b)
    (hx : Points.map a (ofOver.pointsEquiv U u) = x)
    (hu : topologicalKrullDimAt (h.left.asFiber u) = (d : WithBot ℕ∞)) :
    RelativeDimensionEqAt f d x :=
  sorry

/-- If `f` has relative dimension `d` at `x`, then any étale scheme square
through `x` has `dim_u(U_v) = d`. -/
theorem apply {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {d : ℕ∞}
    {x : Points X} (hf : RelativeDimensionEqAt f d x) {U V : Over S}
    (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V) (u : U.left)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (hx : Points.mapOfOver a u = x) :
    topologicalKrullDimAt (h.left.asFiber u) = (d : WithBot ℕ∞) :=
  sorry

end RelativeDimensionEqAt

/-- Given one étale scheme square over `f` with a germ mapping to `x`, exact
relative dimension `d` at `x` is equivalent to the local topological Krull
dimension of the scheme-theoretic fibre being `d` at that germ. -/
theorem relativeDimensionEqAt_iff_of_etale {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} {d : ℕ∞} {x : Points X}
    {U V : Over S} {a : ofOver U ⟶ X} {b : ofOver V ⟶ Y} {h : U ⟶ V}
    {u : U.left} (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b)
    (hx : Points.map a (ofOver.pointsEquiv U u) = x) :
    RelativeDimensionEqAt f d x ↔
      topologicalKrullDimAt (h.left.asFiber u) = (d : WithBot ℕ∞) :=
  sorry

/-- On a morphism of schemes over `S`, viewed as a morphism of algebraic spaces,
the relative dimension at the image of `u` is `d` if and only if
`dim_u(U_v) = d`. -/
theorem relativeDimensionEqAt_ofOverMap_iff {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) (d : ℕ∞) (u : U.left) :
    RelativeDimensionEqAt (ofOverMap h) d (ofOver.pointsEquiv U u) ↔
      topologicalKrullDimAt (h.left.asFiber u) = (d : WithBot ℕ∞) :=
  sorry

/-- A morphism has finite relative dimension `d` at `x` when its local
fibre dimension is `d`. This is the specialization of `RelativeDimensionEqAt`
to the natural number `d`, regarded as an extended natural number. -/
def RelativeDimensionAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ) (x : Points X) : Prop :=
  RelativeDimensionEqAt f (d : ℕ∞) x

/-- Relative dimension `d` at a point is the existence of an étale scheme
presentation whose scheme-theoretic fibre has local topological Krull dimension
`d` at a germ mapping to that point. -/
theorem relativeDimensionAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ) (x : Points X) :
    RelativeDimensionAt f d x ↔
      ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
        (u : U.left),
        (over (@AlgebraicGeometry.Etale)).presheaf a ∧
          (over (@AlgebraicGeometry.Etale)).presheaf b ∧
            a ≫ f = ofOverMap h ≫ b ∧
              Points.map a (ofOver.pointsEquiv U u) = x ∧
                topologicalKrullDimAt (h.left.asFiber u) = (d : WithBot ℕ∞) :=
  relativeDimensionEqAt_iff f (d : ℕ∞) x

namespace RelativeDimensionAt

/-- An étale scheme square over `f` whose scheme-theoretic fibre has local
topological Krull dimension `d` at a germ mapping to `x` witnesses exact
relative dimension `d` at `x`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} {d : ℕ}
    {x : Points X} {U V : Over S} {a : ofOver U ⟶ X} {b : ofOver V ⟶ Y}
    {h : U ⟶ V} {u : U.left}
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b)
    (hx : Points.map a (ofOver.pointsEquiv U u) = x)
    (hu : topologicalKrullDimAt (h.left.asFiber u) = (d : WithBot ℕ∞)) :
    RelativeDimensionAt f d x :=
  RelativeDimensionEqAt.of ha hb w hx hu

end RelativeDimensionAt

/-- Given one étale scheme square over `f` with a germ mapping to `x`, exact
relative dimension `d` at `x` is equivalent to the local topological Krull
dimension of the scheme-theoretic fibre being `d` at that germ. -/
theorem relativeDimensionAt_iff_of_etale {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} {d : ℕ} {x : Points X}
    {U V : Over S} {a : ofOver U ⟶ X} {b : ofOver V ⟶ Y} {h : U ⟶ V}
    {u : U.left} (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b)
    (hx : Points.map a (ofOver.pointsEquiv U u) = x) :
    RelativeDimensionAt f d x ↔
      topologicalKrullDimAt (h.left.asFiber u) = (d : WithBot ℕ∞) :=
  relativeDimensionEqAt_iff_of_etale ha hb w hx

/-- Exact relative dimension `d` at a point implies the corresponding upper
bound. -/
theorem relativeDimensionLEAt_of_relativeDimensionAt {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} {f : X ⟶ Y} {d : ℕ} {x : Points X}
    (h : RelativeDimensionAt f d x) : RelativeDimensionLEAt f d x :=
  sorry

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` has relative dimension
at most `d` if it has relative dimension at most `d` at every point of `X`. -/
@[mk_iff]
class RelativeDimensionLE {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ) : Prop where
  /-- The pointwise relative-dimension bound. -/
  relativeDimensionLEAt : ∀ x : Points X, RelativeDimensionLEAt f d x

namespace RelativeDimensionLE

/-- A morphism of relative dimension at most `d` has the bound at a chosen
source point. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (d : ℕ)
    [RelativeDimensionLE f d] (x : Points X) : RelativeDimensionLEAt f d x :=
  sorry

/-- An étale scheme square over a morphism of relative dimension at most `d`
has scheme-theoretic fibre of local topological Krull dimension at most `d` at
every source scheme point. -/
theorem of_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (d : ℕ)
    [RelativeDimensionLE f d] {U V : Over S} {a : ofOver U ⟶ X}
    {b : ofOver V ⟶ Y} {h : U ⟶ V}
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (u : U.left) :
    topologicalKrullDimAt (h.left.asFiber u) ≤ (d : WithBot ℕ∞) :=
  sorry

/-- The identity morphism of an algebraic space has relative dimension at most
`0`. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    RelativeDimensionLE (𝟙 X) 0 :=
  sorry

end RelativeDimensionLE

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` has relative dimension
`d` if it has relative dimension `d` at every point of `X`. -/
@[mk_iff]
class RelativeDimension {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ) : Prop where
  /-- The pointwise exact relative dimension. -/
  relativeDimensionAt : ∀ x : Points X, RelativeDimensionAt f d x

namespace RelativeDimension

/-- A morphism of relative dimension `d` has exact relative dimension `d` at a
chosen source point. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (d : ℕ)
    [RelativeDimension f d] (x : Points X) : RelativeDimensionAt f d x :=
  sorry

/-- An étale scheme square over a morphism of relative dimension `d` has
scheme-theoretic fibre of local topological Krull dimension `d` at every source
scheme point. -/
theorem of_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (d : ℕ)
    [RelativeDimension f d] {U V : Over S} {a : ofOver U ⟶ X}
    {b : ofOver V ⟶ Y} {h : U ⟶ V}
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) (u : U.left) :
    topologicalKrullDimAt (h.left.asFiber u) = (d : WithBot ℕ∞) :=
  sorry

/-- The identity morphism of an algebraic space has relative dimension `0`. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : RelativeDimension (𝟙 X) 0 :=
  sorry

/-- An isomorphism of algebraic spaces has relative dimension `0`. -/
instance of_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [IsIso f] : RelativeDimension f 0 :=
  sorry

end RelativeDimension

/-- A morphism of exact relative dimension `d` has relative dimension at most
`d`. -/
instance (priority := 900) instRelativeDimensionLE_of_relativeDimension
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (d : ℕ)
    [RelativeDimension f d] : RelativeDimensionLE f d :=
  sorry

/-- A morphism of schemes over `S`, viewed as a morphism of algebraic spaces,
has relative dimension at most `d` if and only if every source point of the
underlying scheme morphism has scheme-theoretic fibre of local topological
Krull dimension at most `d`. -/
theorem relativeDimensionLE_ofOverMap_iff {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) (d : ℕ) :
    RelativeDimensionLE (ofOverMap h) d ↔
      ∀ u : U.left, topologicalKrullDimAt (h.left.asFiber u) ≤ (d : WithBot ℕ∞) :=
  sorry

/-- A morphism of schemes over `S`, viewed as a morphism of algebraic spaces,
has relative dimension `d` if and only if every source point of the underlying
scheme morphism has scheme-theoretic fibre of local topological Krull dimension
`d`. -/
theorem relativeDimension_ofOverMap_iff {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) (d : ℕ) :
    RelativeDimension (ofOverMap h) d ↔
      ∀ u : U.left, topologicalKrullDimAt (h.left.asFiber u) = (d : WithBot ℕ∞) :=
  sorry

/-- For a locally finite type morphism of algebraic spaces, fibre-stalk
dimension `d` and residue-field transcendence degree `r` at a point imply
relative dimension `d + r` at that point. -/
theorem relativeDimensionAt_eq_fiberStalkDim_add_trdeg
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] {d r : ℕ∞} {x : Points X}
    (hd : FiberStalkDimEqAt f d x) (hr : ResidueFieldTrdegEqAt f r x) :
    RelativeDimensionEqAt f (d + r) x :=
  sorry

/-- If `f` has relative dimension `e` at `x`, fibre-stalk dimension `d` at `x`,
and residue-field transcendence degree `r` at `x`, then `e = d + r`. -/
theorem relativeDimensionAt_add_eq {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [LocallyOfFiniteType f] {d r e : ℕ∞} {x : Points X}
    (he : RelativeDimensionEqAt f e x) (hd : FiberStalkDimEqAt f d x)
    (hr : ResidueFieldTrdegEqAt f r x) :
    e = d + r :=
  sorry

/-- On any étale scheme square over a locally finite type morphism of algebraic
spaces, the local topological Krull dimension of the scheme-theoretic fibre
equals the Krull dimension of the fibre stalk plus the residue-field
transcendence degree. -/
theorem etaleSquare_topologicalKrullDimAt_eq_stalk_add_trdeg
    {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFiniteType f] {U V : Over S} (a : ofOver U ⟶ X)
    (b : ofOver V ⟶ Y) (h : U ⟶ V) (u : U.left)
    (ha : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b) :
    topologicalKrullDimAt (h.left.asFiber u) =
      ringKrullDim (Scheme.Hom.fiberStalkAt h.left u) +
        Scheme.Hom.residueFieldTrdegAt h.left u :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
