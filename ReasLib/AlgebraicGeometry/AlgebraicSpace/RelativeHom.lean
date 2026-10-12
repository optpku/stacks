/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-!
# Relative morphisms of algebraic spaces

A test morphism `a : ofOver T ⟶ B` determines fibre products `pullback a z` and
`pullback a x`. A relative morphism over `ofOver T` is an arrow between those
objects in `Over (ofOver T)`. Pairs `(a, b)` package the test morphism with that
arrow.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.RelativeHom

/-- Morphisms over `ofOver T` between the fibre products `pullback a z` and
`pullback a x`. -/
abbrev BaseChangeMorphism {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
    {B Z X : AlgebraicSpace S}
    (z : Z ⟶ B) (x : X ⟶ B) {T : Over S} (a : ofOver T ⟶ B) : Type (u + 1) :=
  Over.mk (pullback.fst a z) ⟶ Over.mk (pullback.fst a x)

/-- A pair `(a, b)` consisting of a test morphism `a : ofOver T ⟶ B` and a
morphism `b` over `ofOver T` from `pullback a z` to `pullback a x`. -/
structure Pair {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B Z X : AlgebraicSpace S}
    (z : Z ⟶ B) (x : X ⟶ B) (T : Over S) : Type (u + 1) where
  /-- The test morphism `a : ofOver T ⟶ B`. -/
  a : ofOver T ⟶ B
  /-- The morphism over `ofOver T` between the fibre products with `Z` and `X`. -/
  b : BaseChangeMorphism z x a

/-- Construct a pair from a test morphism `a` and a morphism `b` over `ofOver T`. -/
def mk {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)] {B Z X : AlgebraicSpace S}
    {z : Z ⟶ B} {x : X ⟶ B}
    {T : Over S} (a : ofOver T ⟶ B) (b : BaseChangeMorphism z x a) : Pair z x T where
  a := a
  b := b

namespace BaseChangeMorphism

/-- The underlying arrow of `b` commutes with the projections to `ofOver T`. -/
theorem over_fst {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
    {B Z X : AlgebraicSpace S} {z : Z ⟶ B} {x : X ⟶ B}
    {T : Over S} {a : ofOver T ⟶ B} (b : BaseChangeMorphism z x a) :
    b.left ≫ pullback.fst a x = pullback.fst a z := sorry

/-- View `b` as a morphism `pullback a z ⟶ X`. -/
def toMap {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
    {B Z X : AlgebraicSpace S} {z : Z ⟶ B} {x : X ⟶ B}
    {T : Over S} {a : ofOver T ⟶ B} (b : BaseChangeMorphism z x a) :
    pullback a z ⟶ X :=
  b.left ≫ pullback.snd a x

/-- The morphism `toMap b` makes the triangle over `B` commute. -/
theorem toMap_comm {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
    {B Z X : AlgebraicSpace S} {z : Z ⟶ B} {x : X ⟶ B}
    {T : Over S} {a : ofOver T ⟶ B} (b : BaseChangeMorphism z x a) :
    toMap b ≫ x = pullback.fst a z ≫ a := sorry

/-- The morphism `pullback a z ⟶ pullback a x` induced by a map to `X` making the
triangle over `B` commute. -/
def ofMap_left {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
    {B Z X : AlgebraicSpace S} {z : Z ⟶ B} {x : X ⟶ B}
    {T : Over S} {a : ofOver T ⟶ B} (b' : pullback a z ⟶ X)
    (h : b' ≫ x = pullback.fst a z ≫ a) : pullback a z ⟶ pullback a x :=
  pullback.lift (pullback.fst a z) b' h.symm

/-- `ofMap_left b' h` projects to `ofOver T` as `pullback.fst a z`. -/
theorem ofMap_left_fst {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
    {B Z X : AlgebraicSpace S} {z : Z ⟶ B} {x : X ⟶ B}
    {T : Over S} {a : ofOver T ⟶ B} (b' : pullback a z ⟶ X)
    (h : b' ≫ x = pullback.fst a z ≫ a) :
    ofMap_left b' h ≫ pullback.fst a x = pullback.fst a z := sorry

/-- Reconstruct a morphism over `ofOver T` from a map `pullback a z ⟶ X` making
the triangle over `B` commute. -/
def ofMap {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
    {B Z X : AlgebraicSpace S} {z : Z ⟶ B} {x : X ⟶ B}
    {T : Over S} {a : ofOver T ⟶ B} (b' : pullback a z ⟶ X)
    (h : b' ≫ x = pullback.fst a z ≫ a) : BaseChangeMorphism z x a :=
  Over.homMk (ofMap_left b' h) (ofMap_left_fst b' h)

/-- `ofMap` recovers `b` from `toMap b`. -/
theorem ofMap_toMap {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
    {B Z X : AlgebraicSpace S} {z : Z ⟶ B} {x : X ⟶ B}
    {T : Over S} {a : ofOver T ⟶ B} (b : BaseChangeMorphism z x a) :
    ofMap (toMap b) (toMap_comm b) = b := sorry

/-- `toMap` recovers the original map into `X` from `ofMap`. -/
theorem toMap_ofMap {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
    {B Z X : AlgebraicSpace S} {z : Z ⟶ B} {x : X ⟶ B}
    {T : Over S} {a : ofOver T ⟶ B} (b' : pullback a z ⟶ X)
    (h : b' ≫ x = pullback.fst a z ≫ a) : toMap (ofMap b' h) = b' := sorry

end BaseChangeMorphism

/-- The components of a pair are a test morphism and a morphism over `ofOver T`. -/
theorem Pair.spec {S : Scheme.{u}} [HasPullbacks (AlgebraicSpace S)]
    {B Z X : AlgebraicSpace S} {z : Z ⟶ B} {x : X ⟶ B}
    {T : Over S} (p : Pair z x T) :
    p.b.left ≫ pullback.fst p.a x = pullback.fst p.a z := sorry

end AlgebraicGeometry.AlgebraicSpace.RelativeHom
