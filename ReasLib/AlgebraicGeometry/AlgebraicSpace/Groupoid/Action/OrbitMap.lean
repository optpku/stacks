/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Action
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Restriction
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Groupoid.Saturation

/-!
# Orbit maps of group algebraic space actions

Orbit maps describe the action on a family of points and compare its sheaf
surjectivity with the saturation map of the restricted action groupoid.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory
open GroupoidAlgebraicSpace
open scoped CategoryTheory.MonObj

noncomputable section

universe u

namespace AlgebraicGeometry.GroupAlgebraicSpace.Action

/-- The orbit map `(g, x') ↦ a(g, φ(x'))` associated to a morphism `φ : X' ⟶ X`
over `B`. -/
def orbitMap {S : Scheme.{u}} {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B)
    (X : Action G) {X' : Over B} (φ : X' ⟶ X.X) : G.X ⊗ X' ⟶ X.X :=
  (G.X ◁ φ) ≫ actionTarget G X

/-- The orbit map is whiskering `φ` followed by the action map. -/
theorem orbitMap_def {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : Action G) {X' : Over B} (φ : X' ⟶ X.X) :
    orbitMap G X φ = (G.X ◁ φ) ≫ actionTarget G X := sorry

/-- On `T`-points over `B`, the orbit map sends `(g, x')` to `a(g, φ(x'))`. -/
theorem orbitMap_apply {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : Action G) {X' : Over B} (φ : X' ⟶ X.X)
    {T : Over B} (g : T ⟶ G.X) (x' : T ⟶ X') :
    lift g x' ≫ orbitMap G X φ = g • (x' ≫ φ) := sorry

/-- A `T`-point of the restricted arrow space `X''` from `x₂` to `x₁` corresponds
to a `T`-point `g` of `G` satisfying `φ(x'₁) = a(g, φ(x'₂))`. -/
theorem restriction_pointHom_iff {S : Scheme.{u}} {B : AlgebraicSpace S}
    (G : GroupAlgebraicSpace B) (X : Action G) {X' : Over B} (φ : X' ⟶ X.X)
    {T : Over S} {σ : AlgebraicSpace.ofOver T ⟶ B} {x₁ x₂ : Over.mk σ ⟶ X'} :
    Nonempty (((ofAction G X).pullback φ).PointHom σ x₂ x₁) ↔
      ∃ g : Over.mk σ ⟶ G.X, x₁ ≫ φ = g • (x₂ ≫ φ) := sorry

/-- The orbit map is an fppf sheaf surjection if and only if the saturation map
of the restricted action groupoid is, via inversion in `G`. -/
theorem locallySurjective_orbitMap_iff_saturationMap {S : Scheme.{u}}
    {B : AlgebraicSpace S} (G : GroupAlgebraicSpace B) (X : Action G)
    {X' : Over B} (φ : X' ⟶ X.X) :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
        (orbitMap G X φ).left ↔
      Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
        ((ofAction G X).saturationMap φ).left := sorry

end AlgebraicGeometry.GroupAlgebraicSpace.Action
