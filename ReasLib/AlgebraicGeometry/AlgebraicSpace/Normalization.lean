/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Finite

/-!
# Relative normalization of algebraic spaces

A factorization `Y ⟶ X' ⟶ X` is a relative normalization of `X` in `Y` when the
map `X' ⟶ X` is integral and initial among integral factorizations of `Y ⟶ X`.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A factorization `toN ≫ fromN = f` exhibits `X'` as the normalization of `X` in `Y`
when `fromN` is integral and initial among integral factorizations of `f`. -/
structure IsNormalization {S : Scheme.{u}} {X Y X' : AlgebraicSpace S}
    (f : Y ⟶ X) (toN : Y ⟶ X') (fromN : X' ⟶ X) : Prop where
  /-- The two maps factor `f`. -/
  factor : toN ≫ fromN = f
  /-- The map from the intermediate space to `X` is integral. -/
  isIntegral : IsIntegralHom fromN
  /-- Any integral factorization of `f` admits a unique comparison morphism from `X'`. -/
  existsUnique_lift : ∀ {Z : AlgebraicSpace S} (g : Y ⟶ Z) (π : Z ⟶ X)
    [IsIntegralHom π], f = g ≫ π → ∃! h : X' ⟶ Z, toN ≫ h = g ∧ h ≫ π = fromN

/-- Unfolding of `IsNormalization` into a commuting triangle, integrality, and the
unique-lift property. -/
theorem isNormalization_iff {S : Scheme.{u}} {X Y X' : AlgebraicSpace S}
    (f : Y ⟶ X) (toN : Y ⟶ X') (fromN : X' ⟶ X) :
    IsNormalization f toN fromN ↔
      toN ≫ fromN = f ∧ IsIntegralHom fromN ∧
        ∀ {Z : AlgebraicSpace S} (g : Y ⟶ Z) (π : Z ⟶ X) [IsIntegralHom π],
          f = g ≫ π → ∃! h : X' ⟶ Z, toN ≫ h = g ∧ h ≫ π = fromN :=
  sorry

namespace IsNormalization

/-- A commuting triangle, integrality of `fromN`, and the unique-lift property
assemble into `IsNormalization`. -/
def of {S : Scheme.{u}} {X Y X' : AlgebraicSpace S} {f : Y ⟶ X}
    {toN : Y ⟶ X'} {fromN : X' ⟶ X} (h_factor : toN ≫ fromN = f)
    (h_isIntegral : IsIntegralHom fromN)
    (h_existsUnique_lift :
      ∀ {Z : AlgebraicSpace S} (g : Y ⟶ Z) (π : Z ⟶ X) [IsIntegralHom π],
        f = g ≫ π → ∃! h : X' ⟶ Z, toN ≫ h = g ∧ h ≫ π = fromN) :
    IsNormalization f toN fromN :=
  ⟨h_factor, h_isIntegral, h_existsUnique_lift⟩

/-- An `IsNormalization` factorization commutes, has integral structure morphism, and
is initial among integral factorizations. -/
theorem spec {S : Scheme.{u}} {X Y X' : AlgebraicSpace S} {f : Y ⟶ X}
    {toN : Y ⟶ X'} {fromN : X' ⟶ X} (h : IsNormalization f toN fromN) :
    toN ≫ fromN = f ∧ IsIntegralHom fromN ∧
      ∀ {Z : AlgebraicSpace S} (g : Y ⟶ Z) (π : Z ⟶ X) [IsIntegralHom π],
        f = g ≫ π → ∃! h' : X' ⟶ Z, toN ≫ h' = g ∧ h' ≫ π = fromN :=
  sorry

/-- Any two relative-normalization factorizations of the same morphism admit a unique
comparison morphism compatible with the maps from `Y` and the maps to `X`. -/
theorem existsUnique_hom {S : Scheme.{u}} {X Y X₁ X₂ : AlgebraicSpace S}
    {f : Y ⟶ X} {to₁ : Y ⟶ X₁} {from₁ : X₁ ⟶ X} {to₂ : Y ⟶ X₂} {from₂ : X₂ ⟶ X}
    (h₁ : IsNormalization f to₁ from₁) (h₂ : IsNormalization f to₂ from₂) :
    ∃! h : X₁ ⟶ X₂, to₁ ≫ h = to₂ ∧ h ≫ from₂ = from₁ :=
  sorry

end IsNormalization

end AlgebraicGeometry.AlgebraicSpace
