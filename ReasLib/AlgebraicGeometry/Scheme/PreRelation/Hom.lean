/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.Scheme.PreRelation

/-!
# Morphisms of scheme pre-relations

This module defines morphisms of scheme pre-relations, their elementary operations, and
cartesian morphisms.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

noncomputable section

namespace AlgebraicGeometry.Scheme.PreRelation

universe u

/-- A morphism of scheme pre-relations consists of compatible maps on objects and arrows. -/
structure Hom {S : Scheme.{u}} {U U' : Over S} (P : PreRelation U)
    (Q : PreRelation U') where
  /-- The map between the objects carrying the relations. -/
  obj : U ⟶ U'
  /-- The map between the objects of related pairs. -/
  arrow : P.left ⟶ Q.left
  /-- Compatibility with the source projection. -/
  map_s : P.s ≫ obj = arrow ≫ Q.s
  /-- Compatibility with the target projection. -/
  map_t : P.t ≫ obj = arrow ≫ Q.t

namespace Hom

/-- Construct a morphism of pre-relations from a commutative square between their defining
maps to the products. -/
def ofDefiningMap {S : Scheme.{u}} {U U' : Over S} {P : PreRelation U}
    {Q : PreRelation U'} (obj : U ⟶ U') (arrow : P.left ⟶ Q.left)
    (map_hom : P.hom ≫ prod.map obj obj = arrow ≫ Q.hom) : Hom P Q where
  obj := obj
  arrow := arrow
  map_s := sorry
  map_t := sorry

/-- The object map of `ofDefiningMap obj arrow map_hom` is `obj`. -/
theorem ofDefiningMap_obj {S : Scheme.{u}} {U U' : Over S} {P : PreRelation U}
    {Q : PreRelation U'} (obj : U ⟶ U') (arrow : P.left ⟶ Q.left)
    (map_hom : P.hom ≫ prod.map obj obj = arrow ≫ Q.hom) :
    (ofDefiningMap obj arrow map_hom).obj = obj := sorry

/-- The arrow map of `ofDefiningMap obj arrow map_hom` is `arrow`. -/
theorem ofDefiningMap_arrow {S : Scheme.{u}} {U U' : Over S} {P : PreRelation U}
    {Q : PreRelation U'} (obj : U ⟶ U') (arrow : P.left ⟶ Q.left)
    (map_hom : P.hom ≫ prod.map obj obj = arrow ≫ Q.hom) :
    (ofDefiningMap obj arrow map_hom).arrow = arrow := sorry

/-- A morphism of pre-relations commutes with the defining maps to the products. -/
theorem map_hom {S : Scheme.{u}} {U U' : Over S} {P : PreRelation U}
    {Q : PreRelation U'} (f : Hom P Q) :
    P.hom ≫ prod.map f.obj f.obj = f.arrow ≫ Q.hom := sorry

/-- The identity morphism of a scheme pre-relation. -/
def id {S : Scheme.{u}} {U : Over S} (P : PreRelation U) : Hom P P where
  obj := 𝟙 U
  arrow := 𝟙 P.left
  map_s := sorry
  map_t := sorry

/-- The composite of two morphisms of scheme pre-relations. -/
def comp {S : Scheme.{u}} {U U' U'' : Over S} {P : PreRelation U}
    {Q : PreRelation U'} {R : PreRelation U''} (f : Hom P Q) (g : Hom Q R) : Hom P R where
  obj := f.obj ≫ g.obj
  arrow := f.arrow ≫ g.arrow
  map_s := sorry
  map_t := sorry

/-- A morphism of pre-relations is cartesian when its square formed by the source maps is a
pullback square of schemes. -/
def IsCartesian {S : Scheme.{u}} {U U' : Over S} {P : PreRelation U}
    {Q : PreRelation U'} (f : Hom P Q) : Prop :=
  IsPullback f.arrow.left P.s.left Q.s.left f.obj.left

/-- Cartesianity is exactly the pullback condition on the arrow, source, and object maps. -/
theorem isCartesian_iff {S : Scheme.{u}} {U U' : Over S} {P : PreRelation U}
    {Q : PreRelation U'} (f : Hom P Q) :
    f.IsCartesian ↔ IsPullback f.arrow.left P.s.left Q.s.left f.obj.left := sorry

/-- A morphism of pre-relations sends related points to related points. -/
theorem mapPointRel {S : Scheme.{u}} {U U' T : Over S} {P : PreRelation U}
    {Q : PreRelation U'} (f : Hom P Q) {x y : T ⟶ U} (h : P.pointRel T x y) :
    Q.pointRel T (x ≫ f.obj) (y ≫ f.obj) := sorry

end Hom

end AlgebraicGeometry.Scheme.PreRelation
