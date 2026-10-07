module

public import ReasLib.AlgebraicGeometry.Scheme.Unibranch
public import stacks_project.Chap66.Definition_66_22_2_EtaleLocalRing
public import stacks_project.Chap66.Lemma_66_4_2_Comparison
public import stacks_project.Chap66.Lemma_66_5_5_PointsTopology
public import stacks_project.Chap66.Lemma_66_16_4_Etale

/-!
# Geometric unibranchness of algebraic spaces

An algebraic space is geometrically unibranch at a point when every étale scheme chart
through that point is geometrically unibranch there. The global property is the pointwise
condition at every point of `|X|`. This is consistent with the corresponding notions for
schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space `X` is geometrically unibranch at a point `x` if
`U.left.isGeometricallyUnibranchAt u` for every étale morphism `a : ofOver U ⟶ X` from a
scheme over `S` with `Points.mapOfOver a u = x`. -/
@[mk_iff]
class GeometricallyUnibranchAt {S : Scheme.{u}} (X : AlgebraicSpace S) (x : Points X) : Prop where
  /-- Every étale scheme chart through `x` is geometrically unibranch at the selected point. -/
  of_etale {U : Over S} (a : ofOver U ⟶ X) (u : U.left) (ha : Etale a)
    (hx : Points.mapOfOver a u = x) : U.left.isGeometricallyUnibranchAt u

namespace GeometricallyUnibranchAt

/-- Geometric unibranchness at a point implies that every étale scheme chart through that
point is geometrically unibranch at the selected point. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    [GeometricallyUnibranchAt X x] {U : Over S} (a : ofOver U ⟶ X) (u : U.left)
    (ha : Etale a) (hx : Points.mapOfOver a u = x) :
    U.left.isGeometricallyUnibranchAt u :=
  sorry

/-- The condition that every étale scheme chart through `x` is geometrically unibranch at
the selected point witnesses geometric unibranchness at `x`. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X}
    (h : ∀ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
      Etale a → Points.mapOfOver a u = x → U.left.isGeometricallyUnibranchAt u) :
    GeometricallyUnibranchAt X x :=
  sorry

/-- Geometric unibranchness at `x` is equivalent to unique minimal primes of the local ring
of every étale scheme chart through `x`. -/
theorem iff_uniqueMinimalPrime {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X} :
    GeometricallyUnibranchAt X x ↔
      ∀ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
        Etale a → Points.mapOfOver a u = x →
          ∃! p : Ideal (U.left.presheaf.stalk u), p ∈ minimalPrimes (U.left.presheaf.stalk u) :=
  sorry

/-- Geometric unibranchness at `x` is equivalent to unibranchness of every étale scheme
chart through `x` at the selected point. -/
theorem iff_isUnibranchAt {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X} :
    GeometricallyUnibranchAt X x ↔
      ∀ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
        Etale a → Points.mapOfOver a u = x → U.left.isUnibranchAt u :=
  sorry

/-- Geometric unibranchness at `x` is equivalent to unique minimal primes of the étale local
ring at every geometric point lying over `x`. -/
theorem iff_etaleLocalRing {S : Scheme.{u}} {X : AlgebraicSpace S} {x : Points X} :
    GeometricallyUnibranchAt X x ↔
      ∀ xbar : GeometricPoint X, xbar.liesOver x →
        ∃! p : Ideal (etaleLocalRing X xbar), p ∈ minimalPrimes (etaleLocalRing X xbar) :=
  sorry

end GeometricallyUnibranchAt

/-- A scheme over `S`, viewed as an algebraic space, is geometrically unibranch at a point
whenever the corresponding scheme stalk is geometrically unibranch. -/
instance instGeometricallyUnibranchAt_ofOver {S : Scheme.{u}} {T : Over S} {t : T.left}
    [h : _root_.IsGeometricallyUnibranch (T.left.presheaf.stalk t)] :
    GeometricallyUnibranchAt (ofOver T) (ofOver.pointsEquiv T t) :=
  sorry

/-- On a scheme over `S`, viewed as an algebraic space, geometric unibranchness at a point
is the usual geometric unibranchness of the scheme at that point. -/
theorem geometricallyUnibranchAt_ofOver_iff {S : Scheme.{u}} (T : Over S) (t : T.left) :
    GeometricallyUnibranchAt (ofOver T) (ofOver.pointsEquiv T t) ↔
      T.left.isGeometricallyUnibranchAt t :=
  sorry

/-- An algebraic space is geometrically unibranch if it is geometrically unibranch at every
point of `|X|`. -/
@[mk_iff]
class IsGeometricallyUnibranch {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- Geometric unibranchness holds at every point of `|X|`. -/
  unibranchAt : ∀ x : Points X, GeometricallyUnibranchAt X x

namespace IsGeometricallyUnibranch

/-- A geometrically unibranch algebraic space is geometrically unibranch at every point. -/
theorem spec {S : Scheme.{u}} {X : AlgebraicSpace S} [IsGeometricallyUnibranch X] :
    ∀ x : Points X, GeometricallyUnibranchAt X x :=
  sorry

/-- The condition that `X` is geometrically unibranch at every point witnesses that `X` is
geometrically unibranch. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S}
    (h : ∀ x : Points X, GeometricallyUnibranchAt X x) : IsGeometricallyUnibranch X :=
  sorry

end IsGeometricallyUnibranch

/-- A geometrically unibranch algebraic space is geometrically unibranch at each of its
points. -/
instance instGeometricallyUnibranchAt {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsGeometricallyUnibranch X] (x : Points X) : GeometricallyUnibranchAt X x :=
  sorry

/-- A geometrically unibranch scheme over `S`, viewed as an algebraic space, is
geometrically unibranch. -/
instance instIsGeometricallyUnibranch_ofOver {S : Scheme.{u}} {T : Over S}
    [h : ∀ t : T.left, _root_.IsGeometricallyUnibranch (T.left.presheaf.stalk t)] :
    IsGeometricallyUnibranch (ofOver T) :=
  sorry

/-- A scheme over `S`, viewed as an algebraic space, is geometrically unibranch if and only
if the underlying scheme is geometrically unibranch. -/
theorem isGeometricallyUnibranch_ofOver_iff {S : Scheme.{u}} (T : Over S) :
    IsGeometricallyUnibranch (ofOver T) ↔ T.left.isGeometricallyUnibranch :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
