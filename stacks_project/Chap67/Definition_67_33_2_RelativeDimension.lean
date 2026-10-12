/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import ReasLib.Topology.KrullDimension.Local
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Lemma_66_4_2_Comparison

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
def RelativeDimensionAt {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (d : ℕ) (x : Points X) : Prop :=
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
  sorry

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
  sorry

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
  sorry

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

end AlgebraicGeometry.AlgebraicSpace
