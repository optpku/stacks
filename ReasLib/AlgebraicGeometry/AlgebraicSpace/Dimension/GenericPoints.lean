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
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Decent.Etale
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

private theorem exists_etaleChart_through {S : Scheme.{u}} {X : AlgebraicSpace S}
    (x : Points X) :
    ∃ (U : Over S) (a : ofOver U ⟶ X) (u : U.left),
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf a ∧
        Points.mapOfOver a u = x := by
  obtain ⟨U, a, ha, hsurj⟩ := X.atlas
  obtain ⟨u, hu⟩ := (Points.isOpenQuotientMap_mapOfOver a ha hsurj).surjective x
  exact ⟨U, a, u, ha, hu⟩

/-- A point of an algebraic space has local-ring dimension zero if and only if some point
above it in an étale scheme chart is a generic point of an irreducible component. -/
theorem localRingDimAt_eq_zero_iff_existsEtaleAt_mem_genericPoints
    {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) :
    localRingDimAt x = 0 ↔ existsEtaleAt (fun U u ↦ u ∈ _root_.genericPoints U) X x := by
  constructor
  · intro hx
    obtain ⟨U, a, u, ha, hu⟩ := exists_etaleChart_through x
    refine ⟨U, a, u, ha, hu, ?_⟩
    apply (Scheme.mem_genericPoints_iff_ringKrullDim_stalk_eq_zero u).mpr
    rw [← localRingDimAt_eq_ringKrullDim_stalk a ha u hu]
    exact hx
  · rintro ⟨U, a, u, ha, hu, hgeneric⟩
    rw [localRingDimAt_eq_ringKrullDim_stalk a ha u hu]
    exact (Scheme.mem_genericPoints_iff_ringKrullDim_stalk_eq_zero u).mp hgeneric

/-- A point of an algebraic space has local-ring dimension zero if and only if every point
above it in every étale scheme chart is a generic point of an irreducible component. -/
theorem localRingDimAt_eq_zero_iff_forallEtaleAt_mem_genericPoints
    {S : Scheme.{u}} {X : AlgebraicSpace S} (x : Points X) :
    localRingDimAt x = 0 ↔ forallEtaleAt (fun U u ↦ u ∈ _root_.genericPoints U) X x := by
  constructor
  · intro hx U a u ha hu
    apply (Scheme.mem_genericPoints_iff_ringKrullDim_stalk_eq_zero u).mpr
    rw [← localRingDimAt_eq_ringKrullDim_stalk a ha u hu]
    exact hx
  · intro h
    obtain ⟨U, a, u, ha, hu⟩ := exists_etaleChart_through x
    exact (localRingDimAt_eq_zero_iff_existsEtaleAt_mem_genericPoints x).mpr
      ⟨U, a, u, ha, hu, h U a u ha hu⟩

/-- On a scheme viewed as an algebraic space, a point has local-ring dimension zero if and
only if the corresponding scheme point is a generic point of an irreducible component. -/
theorem localRingDimAt_eq_zero_iff_mem_genericPoints_ofOver
    {S : Scheme.{u}} (T : Over S) (t : T.left) :
    localRingDimAt (ofOver.pointsEquiv T t) = 0 ↔ t ∈ _root_.genericPoints T.left := by
  rw [localRingDimAt_ofOver]
  exact (Scheme.mem_genericPoints_iff_ringKrullDim_stalk_eq_zero t).symm

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
      , x ∈ codimZeroPoints X ] := by
  have hgeneric {Z : AlgebraicSpace S} [IsDecent Z] (z : Points Z) :
      z ∈ genericPoints Z ↔ localRingDimAt z = 0 := by
    let T : TopologicalSpace.IrreducibleCloseds (Points Z) :=
      ⟨closure {z}, isIrreducible_singleton.closure, isClosed_closure⟩
    rw [localRingDimAt_eq_coheight T z isGenericPoint_closure,
      WithBot.coe_eq_zero, Order.coheight_eq_zero]
    change closure {z} ∈ irreducibleComponents (Points Z) ↔ IsMax T
    constructor
    · intro hz W hTW
      exact hz.2 W.isIrreducible hTW
    · intro hT
      refine ⟨isIrreducible_singleton.closure, ?_⟩
      intro W hW hTW
      exact Set.Subset.trans subset_closure
        (hT (show T ≤ TopologicalSpace.IrreducibleCloseds.mk (closure W) hW.closure
          isClosed_closure from Set.Subset.trans hTW subset_closure))
  have hdim (Y : AlgebraicSpace S) (f : Y ⟶ X) (hf : Etale f) (y : Points Y) :
      localRingDimAt (Points.map f y) = localRingDimAt y := by
    obtain ⟨U, a, u, ha, hu⟩ := exists_etaleChart_through y
    have hcomp : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf (a ≫ f) :=
      hf.of_etale a ha
    have hmap : Points.mapOfOver (a ≫ f) u = Points.map f y := by
      change Points.map (a ≫ f) (ofOver.pointsEquiv U u) = Points.map f y
      rw [Points.map_comp]
      exact congrArg (Points.map f) hu
    exact (localRingDimAt_eq_ringKrullDim_stalk (a ≫ f) hcomp u hmap).trans
      (localRingDimAt_eq_ringKrullDim_stalk a ha u hu).symm
  have hforall :
      (∀ (Y : AlgebraicSpace S) (f : Y ⟶ X) (y : Points Y),
        Etale f → Points.map f y = x → y ∈ genericPoints Y) ↔ localRingDimAt x = 0 := by
    constructor
    · intro h
      exact (hgeneric x).mp (h X (𝟙 X) x inferInstance (Points.map_id x))
    · intro hx Y f y hf hy
      letI : Etale f := hf
      letI : IsDecent Y := IsDecent.of_etale f
      apply (hgeneric y).mpr
      rw [← hdim Y f hf y, hy]
      exact hx
  have hexists :
      (∃ (Y : AlgebraicSpace S) (f : Y ⟶ X) (y : Points Y),
        Etale f ∧ Points.map f y = x ∧ y ∈ genericPoints Y) ↔ localRingDimAt x = 0 := by
    constructor
    · rintro ⟨Y, f, y, hf, hy, hgeneric_y⟩
      letI : Etale f := hf
      letI : IsDecent Y := IsDecent.of_etale f
      rw [← hy, hdim Y f hf y]
      exact (hgeneric y).mp hgeneric_y
    · intro hx
      exact ⟨X, 𝟙 X, x, inferInstance, Points.map_id x, (hgeneric x).mpr hx⟩
  apply List.tfae_of_forall (localRingDimAt x = 0)
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact hgeneric x
  · exact hforall
  · exact hexists
  · rfl
  · rfl

/-- On a decent algebraic space, a point is generic on `|X|` if and only if the
dimension of the local ring at that point is zero. -/
theorem mem_genericPoints_iff_localRingDimAt_eq_zero {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] {x : Points X} :
    x ∈ genericPoints X ↔ localRingDimAt x = 0 :=
  (mem_genericPoints_tfae x).out 0 3

/-- On a decent algebraic space, a point is generic on `|X|` if and only if it is
a point of codimension `0`. -/
theorem mem_genericPoints_iff_mem_codimZeroPoints {S : Scheme.{u}}
    {X : AlgebraicSpace S} [IsDecent X] {x : Points X} :
    x ∈ genericPoints X ↔ x ∈ codimZeroPoints X :=
  (mem_genericPoints_tfae x).out 0 4

/-- On a decent algebraic space, a point `x` is generic on `|X|` if and only if
every étale pointed chart `(Y, y) ⟶ (X, x)` has `y` generic on `|Y|`. -/
theorem mem_genericPoints_iff_forall_etale {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] {x : Points X} :
    x ∈ genericPoints X ↔
      ∀ (Y : AlgebraicSpace S) (f : Y ⟶ X) (y : Points Y),
        Etale f → Points.map f y = x → y ∈ genericPoints Y :=
  (mem_genericPoints_tfae x).out 0 1

/-- On a decent algebraic space, a point `x` is generic on `|X|` if and only if
some étale pointed chart `(Y, y) ⟶ (X, x)` has `y` generic on `|Y|`. -/
theorem mem_genericPoints_iff_exists_etale {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsDecent X] {x : Points X} :
    x ∈ genericPoints X ↔
      ∃ (Y : AlgebraicSpace S) (f : Y ⟶ X) (y : Points Y),
        Etale f ∧ Points.map f y = x ∧ y ∈ genericPoints Y :=
  (mem_genericPoints_tfae x).out 0 2

/-- Membership in `genericPoints` is preserved and reflected by étale morphisms
into a decent algebraic space. -/
theorem mem_genericPoints_map_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    [IsDecent X] (f : Y ⟶ X) (hf : Etale f) {y : Points Y} :
    y ∈ genericPoints Y ↔ Points.map f y ∈ genericPoints X := by
  constructor
  · intro hy
    exact mem_genericPoints_iff_exists_etale.mpr ⟨Y, f, y, hf, rfl, hy⟩
  · intro hx
    exact mem_genericPoints_iff_forall_etale.mp hx Y f y hf rfl

end AlgebraicGeometry.AlgebraicSpace
