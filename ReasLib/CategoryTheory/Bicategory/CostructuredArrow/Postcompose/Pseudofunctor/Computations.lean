/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Bicategory.CostructuredArrow.Postcompose.Pseudofunctor.Basic

/-!
# Computations for postcomposition of costructured arrows

This file exposes the principal fields and nested projections of
`ColaxCostructuredArrow.postcompose`. These formulas let downstream
constructions compute through the public pseudofunctor without unfolding its
private prelax and coherence assembly.
-/

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

open scoped CategoryTheory.Bicategory

universe uA vA wA uC vC wC

namespace CategoryTheory

open Bicategory

namespace Bicategory.ColaxCostructuredArrow

variable {A : Type uA} [Bicategory.{wA, vA} A]
variable {C : Type uC} [Bicategory.{wC, vC} C]
variable {K : Pseudofunctor A C}
variable {X Y : C}

namespace postcompose

/-- The object action of costructured-arrow postcomposition is
`postcompose.obj`. -/
@[simp]
theorem obj.action
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    (postcompose K f).obj S = postcompose.obj f S := sorry

/-- The `1`-morphism action of costructured-arrow postcomposition is
`postcompose.map`. -/
@[simp]
theorem map.action
    (f : X ⟶ Y) {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    (postcompose K f).map u = postcompose.map f u := sorry

/-- The `2`-morphism action of costructured-arrow postcomposition is
`postcompose.map₂`. -/
@[simp]
theorem map₂.action
    (f : X ⟶ Y) {S T : ColaxCostructuredArrow K X}
    {u v : S ⟶ T} (η : u ⟶ v) :
    (postcompose K f).map₂ η = postcompose.map₂ f η := sorry

/-- The identity comparison of costructured-arrow postcomposition is
`postcompose.mapId`. -/
@[simp]
theorem mapId.action
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    (postcompose K f).mapId S = postcompose.mapId f S := sorry

/-- The composition comparison of costructured-arrow postcomposition is
`postcompose.mapComp`. -/
@[simp]
theorem mapComp.action
    (f : X ⟶ Y) {R S T : ColaxCostructuredArrow K X}
    (u : R ⟶ S) (v : S ⟶ T) :
    (postcompose K f).mapComp u v =
      postcompose.mapComp f u v := sorry

/-- Postcomposition leaves the source object of a costructured arrow
unchanged. -/
@[simp]
theorem obj.action.left
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    ((postcompose K f).obj S).left = S.left := sorry

/-- Postcomposition composes the structural map of a costructured arrow with
the target `1`-morphism. -/
@[simp]
theorem obj.action.hom
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    ((postcompose K f).obj S).hom = S.hom ≫ f := sorry

/-- Postcomposition leaves the source map of a costructured-arrow morphism
unchanged. -/
@[simp]
theorem map.action.underlying
    (f : X ⟶ Y) {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    ColaxCostructuredArrow.map (K := K) (X := Y)
        ((postcompose K f).map u) =
      ColaxCostructuredArrow.map (K := K) (X := X) u := sorry

/-- The normalized comparison of a postcomposed morphism is
`postcompose.fac`. -/
@[simp]
theorem map.action.fac
    (f : X ⟶ Y) {S T : ColaxCostructuredArrow K X} (u : S ⟶ T) :
    ColaxCostructuredArrow.fac (K := K) (X := Y)
        ((postcompose K f).map u) =
      postcompose.fac f u := sorry

/-- Postcomposition leaves the source cell of a costructured-arrow
`2`-morphism unchanged. -/
@[simp]
theorem map₂.action.underlying
    (f : X ⟶ Y) {S T : ColaxCostructuredArrow K X}
    {u v : S ⟶ T} (η : u ⟶ v) :
    ColaxCostructuredArrow.map₂ (K := K) (X := Y)
        ((postcompose K f).map₂ η) =
      ColaxCostructuredArrow.map₂ (K := K) (X := X) η := sorry

/-- The forward identity comparison has identity source cell. -/
@[simp]
theorem mapId.action.hom.map₂
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.map₂ (K := K) (X := Y)
        ((postcompose K f).mapId S).hom =
      𝟙 (𝟙 S.left) := sorry

/-- The inverse identity comparison has identity source cell. -/
@[simp]
theorem mapId.action.inv.map₂
    (f : X ⟶ Y) (S : ColaxCostructuredArrow K X) :
    ColaxCostructuredArrow.map₂ (K := K) (X := Y)
        ((postcompose K f).mapId S).inv =
      𝟙 (𝟙 S.left) := sorry

/-- The forward composition comparison has identity source cell. -/
@[simp]
theorem mapComp.action.hom.map₂
    (f : X ⟶ Y) {R S T : ColaxCostructuredArrow K X}
    (u : R ⟶ S) (v : S ⟶ T) :
    ColaxCostructuredArrow.map₂ (K := K) (X := Y)
        ((postcompose K f).mapComp u v).hom =
      𝟙 (ColaxCostructuredArrow.map (K := K) (X := X) u ≫
        ColaxCostructuredArrow.map (K := K) (X := X) v) := sorry

/-- The inverse composition comparison has identity source cell. -/
@[simp]
theorem mapComp.action.inv.map₂
    (f : X ⟶ Y) {R S T : ColaxCostructuredArrow K X}
    (u : R ⟶ S) (v : S ⟶ T) :
    ColaxCostructuredArrow.map₂ (K := K) (X := Y)
        ((postcompose K f).mapComp u v).inv =
      𝟙 (ColaxCostructuredArrow.map (K := K) (X := X) u ≫
        ColaxCostructuredArrow.map (K := K) (X := X) v) := sorry

/- Data and axiom audit (mathlib 4.32):

This module introduces no new data. Every theorem identifies a projection of
`postcompose` with an explicit object, morphism, cell, or comparison owner from
the preceding layers. -/

end postcompose

end Bicategory.ColaxCostructuredArrow

end CategoryTheory
