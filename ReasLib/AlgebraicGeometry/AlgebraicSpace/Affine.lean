/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism

/-!
# Affine algebraic spaces and morphisms

This module records affineness for algebraic spaces and their morphisms over a
scheme.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- An algebraic space over `S` is affine if it is representable by an affine
scheme over `S`. -/
@[mk_iff]
class IsAffine {S : Scheme.{u}} (X : AlgebraicSpace S) : Prop where
  /-- There is an affine scheme over `S` whose associated algebraic space is
  isomorphic to `X`. -/
  exists_affineScheme :
    ∃ (T : Over S), AlgebraicGeometry.IsAffine T.left ∧ Nonempty (X ≅ ofOver T)

namespace IsAffine

/-- An affine algebraic space is isomorphic to the algebraic space associated
to an affine scheme. -/
theorem spec {S : Scheme.{u}} (X : AlgebraicSpace S) [IsAffine X] :
    ∃ (T : Over S), AlgebraicGeometry.IsAffine T.left ∧ Nonempty (X ≅ ofOver T) := sorry

/-- An isomorphism with the algebraic space associated to an affine scheme
witnesses that an algebraic space is affine. -/
theorem of {S : Scheme.{u}} {X : AlgebraicSpace S} {T : Over S}
    [AlgebraicGeometry.IsAffine T.left] (e : X ≅ ofOver T) : IsAffine X := sorry

end IsAffine

/-- The algebraic space associated to an affine scheme is affine. -/
instance instIsAffine_ofOver {S : Scheme.{u}} (T : Over S)
    [hT : AlgebraicGeometry.IsAffine T.left] : IsAffine (ofOver T) where
  exists_affineScheme := ⟨T, hT, ⟨Iso.refl (ofOver T)⟩⟩

/-- The algebraic space associated to a scheme `T` over `S` is affine if and only
if `T` is an affine scheme. -/
theorem isAffine_ofOver_iff {S : Scheme.{u}} (T : Over S) :
    IsAffine (ofOver T) ↔ AlgebraicGeometry.IsAffine T.left := sorry

/-- An algebraic space is affine if and only if its functor of points is
representable by an affine scheme. -/
theorem isAffine_iff_functorOfPoints {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsAffine X ↔
      ∃ (T : Over S), AlgebraicGeometry.IsAffine T.left ∧
        Nonempty (X.functorOfPoints ≅ yoneda.obj T) := sorry

/-- A morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` is affine if for every
affine scheme `Z` and morphism `Z ⟶ Y`, the fibre product `X ×_Y Z` is
representable by an affine scheme. -/
@[mk_iff]
class Affine {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- The vertex of an `IsPullback` square for `f` against an affine scheme is
  an affine algebraic space. -/
  pullback_isAffine {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
      {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X} :
      IsPullback pZ pX g f → IsAffine P

namespace Affine

/-- The identity morphism of an algebraic space is affine. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Affine (𝟙 X) := sorry

/-- An isomorphism of algebraic spaces is affine. -/
instance of_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIso f] :
    Affine f := sorry

/-- Affine morphisms of algebraic spaces are stable under composition. -/
instance isStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Affine S : MorphismProperty (AlgebraicSpace S)) := sorry

/-- The composite of two affine morphisms of algebraic spaces is affine. -/
instance comp {S : Scheme.{u}} {X Y Z : AlgebraicSpace S}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Affine f] [Affine g] :
    Affine (f ≫ g) := sorry

/-- An affine morphism pulls affine schemes back to affine algebraic spaces
along any `IsPullback` square. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} {Z : Over S}
    {P : AlgebraicSpace S} {f : X ⟶ Y} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X} [Affine f] [AlgebraicGeometry.IsAffine Z.left]
    (h : IsPullback pZ pX g f) : IsAffine P := sorry

/-- A universal affine-scheme pullback condition witnesses that a morphism of
algebraic spaces is affine. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left] {P : AlgebraicSpace S}
      {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
      IsPullback pZ pX g f → IsAffine P) : Affine f := sorry

end Affine

/-- The chosen fibre product of an affine morphism with an affine scheme is an
affine algebraic space. -/
instance instIsAffine_pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    {Z : Over S} (f : X ⟶ Y) (g : ofOver Z ⟶ Y) [Affine f]
    [AlgebraicGeometry.IsAffine Z.left] [HasPullback f g] :
    IsAffine (pullback f g) := sorry

end AlgebraicGeometry.AlgebraicSpace
