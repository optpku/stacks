/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.Topology.IrreducibleComponents.AtPoint
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleNeighborhood
public import ReasLib.AlgebraicGeometry.Scheme.Unibranch
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points.Topology
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleLocalRing

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
        ∃! p : Ideal (etaleLocalRing.asCommRing X xbar),
          p ∈ minimalPrimes (etaleLocalRing.asCommRing X xbar) :=
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

section

open TopologicalSpace EtaleNeighborhood

variable {S : Scheme.{u}} {X : AlgebraicSpace S}

/-- Let `S` be a scheme, let `X` be an algebraic space over `S`, and let
`x` be a point of `|X|`. The following are equivalent: for any étale neighbourhood
`U : EtaleNeighborhood X x` the stalk `(scheme U).presheaf.stalk (point U)` has a unique
minimal prime; for any such neighbourhood there is a unique irreducible component of
`scheme U` through `point U`; for any such neighbourhood `scheme U` is unibranch at
`point U`; for any such neighbourhood `scheme U` is geometrically unibranch at
`point U`; and `etaleLocalRing X xbar` has a unique minimal prime for any geometric
point `xbar` lying over `x`. -/
@[stacks 06DK]
theorem etaleLocalRing_uniqueMinimalPrime_tfae (x : Points X) :
    List.TFAE
      [ ∀ U : EtaleNeighborhood X x,
          ∃! p : Ideal ((scheme U).presheaf.stalk (point U)),
            p ∈ minimalPrimes ((scheme U).presheaf.stalk (point U))
      , ∀ U : EtaleNeighborhood X x,
          ∃! Z, Z ∈ irreducibleComponentsAt (point U)
      , ∀ U : EtaleNeighborhood X x,
          (scheme U).isUnibranchAt (point U)
      , ∀ U : EtaleNeighborhood X x,
          (scheme U).isGeometricallyUnibranchAt (point U)
      , ∀ xbar : GeometricPoint X, xbar.liesOver x →
          ∃! p : Ideal (etaleLocalRing X xbar),
            p ∈ minimalPrimes (etaleLocalRing X xbar) ] :=
  sorry

/-- The étale-site stalk at every geometric point over `x` has a unique minimal prime if
and only if every étale neighbourhood of `x` has a unique minimal prime in its local ring
at the selected point. -/
theorem etaleLocalRing_uniqueMinimalPrime_iff_etaleStalk (x : Points X) :
    (∀ xbar : GeometricPoint X, xbar.liesOver x →
        ∃! p : Ideal (etaleLocalRing X xbar),
          p ∈ minimalPrimes (etaleLocalRing X xbar)) ↔
      ∀ U : EtaleNeighborhood X x,
        ∃! p : Ideal ((scheme U).presheaf.stalk (point U)),
          p ∈ minimalPrimes ((scheme U).presheaf.stalk (point U)) :=
  sorry

/-- The étale-site stalk at every geometric point over `x` has a unique minimal prime if
and only if every étale neighbourhood of `x` has a unique irreducible component through
its selected point. -/
theorem etaleLocalRing_uniqueMinimalPrime_iff_uniqueComponent (x : Points X) :
    (∀ xbar : GeometricPoint X, xbar.liesOver x →
        ∃! p : Ideal (etaleLocalRing X xbar),
          p ∈ minimalPrimes (etaleLocalRing X xbar)) ↔
      ∀ U : EtaleNeighborhood X x,
        ∃! Z, Z ∈ irreducibleComponentsAt (point U) :=
  sorry

/-- The étale-site stalk at every geometric point over `x` has a unique minimal prime if
and only if every étale neighbourhood of `x` is unibranch at its selected point. -/
theorem etaleLocalRing_uniqueMinimalPrime_iff_isUnibranchAt (x : Points X) :
    (∀ xbar : GeometricPoint X, xbar.liesOver x →
        ∃! p : Ideal (etaleLocalRing X xbar),
          p ∈ minimalPrimes (etaleLocalRing X xbar)) ↔
      ∀ U : EtaleNeighborhood X x,
        (scheme U).isUnibranchAt (point U) :=
  sorry

/-- The étale-site stalk at every geometric point over `x` has a unique minimal prime if
and only if every étale neighbourhood of `x` is geometrically unibranch at its selected
point. -/
theorem etaleLocalRing_uniqueMinimalPrime_iff_isGeometricallyUnibranchAt (x : Points X) :
    (∀ xbar : GeometricPoint X, xbar.liesOver x →
        ∃! p : Ideal (etaleLocalRing X xbar),
          p ∈ minimalPrimes (etaleLocalRing X xbar)) ↔
      ∀ U : EtaleNeighborhood X x,
        (scheme U).isGeometricallyUnibranchAt (point U) :=
  sorry


end

end AlgebraicGeometry.AlgebraicSpace
