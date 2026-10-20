/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.LocalRing
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Dimension.CodimensionZero
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Point.GenericPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.GermProperty
public import ReasLib.AlgebraicGeometry.Scheme.GenericPoints.Dimension

/-!
# Codimension-zero points of algebraic spaces

Local-ring dimension zero is detected by generic points of irreducible components in étale
scheme charts. On a representable algebraic space, it is the usual generic-point condition.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A point of an algebraic space has local-ring dimension zero if and only if some point
above it in an étale scheme chart is a generic point of an irreducible component. -/
theorem localRingDimAt_eq_zero_iff_existsEtaleAt_mem_genericPoints
    {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) :
    localRingDimAt x = 0 ↔ existsEtaleAt (fun U u ↦ u ∈ _root_.genericPoints U) X x :=
  sorry

/-- A point of an algebraic space has local-ring dimension zero if and only if every point
above it in every étale scheme chart is a generic point of an irreducible component. -/
theorem localRingDimAt_eq_zero_iff_forallEtaleAt_mem_genericPoints
    {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) :
    localRingDimAt x = 0 ↔ forallEtaleAt (fun U u ↦ u ∈ _root_.genericPoints U) X x :=
  sorry

/-- On a scheme viewed as an algebraic space, a point has local-ring dimension zero if and
only if the corresponding scheme point is a generic point of an irreducible component. -/
theorem localRingDimAt_eq_zero_iff_mem_genericPoints_ofOver
    {S : Scheme.{u}} (T : Over S) (t : T.left) :
    localRingDimAt (ofOver.pointsEquiv T t) = 0 ↔ t ∈ _root_.genericPoints T.left :=
  sorry

/-- For a point of a decent algebraic space, being a generic point of an irreducible
component is equivalent to genericity above it along every or some pointed étale morphism,
vanishing local-ring dimension, and codimension zero. -/
@[stacks 0ABV]
theorem mem_genericPoints_tfae {S : Scheme.{u}} {X : AlgebraicSpace S} [IsDecent X]
    (x : Points X) :
    List.TFAE
      [ x ∈ genericPoints X
      , ∀ (Y : AlgebraicSpace S) (f : Y ⟶ X) (y : Points Y),
          Etale f → Points.map f y = x → y ∈ genericPoints Y
      , ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X) (y : Points Y),
          Etale f ∧ Points.map f y = x ∧ y ∈ genericPoints Y
      , localRingDimAt x = 0
      , x ∈ codimZeroPoints X ] :=
  sorry

/-- On a decent algebraic space, a point is generic on `|X|` if and only if the
dimension of the local ring at that point is zero. -/
theorem mem_genericPoints_iff_localRingDimAt_eq_zero {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] {x : Points X} :
    x ∈ genericPoints X ↔ localRingDimAt x = 0 :=
  sorry

/-- On a decent algebraic space, a point is generic on `|X|` if and only if it is
a point of codimension `0`. -/
theorem mem_genericPoints_iff_mem_codimZeroPoints {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] {x : Points X} :
    x ∈ genericPoints X ↔ x ∈ codimZeroPoints X :=
  sorry

/-- On a decent algebraic space, a point `x` is generic on `|X|` if and only if
every étale pointed chart `(Y, y) ⟶ (X, x)` has `y` generic on `|Y|`. -/
theorem mem_genericPoints_iff_forall_etale {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] {x : Points X} :
    x ∈ genericPoints X ↔
      ∀ (Y : AlgebraicSpace S) (f : Y ⟶ X) (y : Points Y),
        Etale f → Points.map f y = x → y ∈ genericPoints Y :=
  sorry

/-- On a decent algebraic space, a point `x` is generic on `|X|` if and only if
some étale pointed chart `(Y, y) ⟶ (X, x)` has `y` generic on `|Y|`. -/
theorem mem_genericPoints_iff_exists_etale {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] {x : Points X} :
    x ∈ genericPoints X ↔
      ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X) (y : Points Y),
        Etale f ∧ Points.map f y = x ∧ y ∈ genericPoints Y :=
  sorry

/-- Membership in `genericPoints` is preserved and reflected by étale morphisms
into a decent algebraic space. -/
theorem mem_genericPoints_map_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] (f : Y ⟶ X) (hf : Etale f) {y : Points Y} :
    y ∈ genericPoints Y ↔ Points.map f y ∈ genericPoints X :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
