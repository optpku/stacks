/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic

/-!
# Local tests for universally injective morphisms of algebraic spaces

Universally injective morphisms of algebraic spaces may be tested on
scheme-valued and affine base change, on a surjective scheme morphism to the
target, and on a Zariski covering of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace UniversallyInjective

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- The projection of every scheme-valued base change of `f` is universally
injective. -/
def forallScheme : Prop :=
  ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → UniversallyInjective pZ

/-- `forallScheme f` means every scheme-valued pullback projection of `f` is
universally injective. -/
theorem forallScheme_iff : forallScheme f ↔
    ∀ (Z : Over S) (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → UniversallyInjective pZ := sorry

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → UniversallyInjective pZ) : forallScheme f := sorry

/-- Under `forallScheme f`, the test-leg of any scheme-valued pullback of `f` is
universally injective. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : UniversallyInjective pZ := sorry

end forallScheme

/-- The projection of every affine-scheme-valued base change of `f` is
universally injective. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → UniversallyInjective pZ

/-- `forallAffine f` means every affine-scheme-valued pullback projection of `f`
is universally injective. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → UniversallyInjective pZ := sorry

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses
`forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → UniversallyInjective pZ) : forallAffine f := sorry

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is universally injective. -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : UniversallyInjective pZ := sorry

end forallAffine

/-- There is a surjective morphism from a scheme to `Y` along which every
pullback of `f` is universally injective. -/
def existsSchemeSurjectiveOnTarget : Prop :=
  ∃ (Z : Over S) (ψ : ofOver Z ⟶ Y),
    Surjective ψ ∧
      ∀ {P : AlgebraicSpace S} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
        IsPullback pZ pX ψ f → UniversallyInjective pZ

/-- `existsSchemeSurjectiveOnTarget f` is the existence of a surjective scheme
morphism to `Y` along which pullbacks of `f` are universally injective. -/
theorem existsSchemeSurjectiveOnTarget_iff : existsSchemeSurjectiveOnTarget f ↔
    ∃ (Z : Over S) (ψ : ofOver Z ⟶ Y),
      Surjective ψ ∧
        ∀ (P : AlgebraicSpace S) (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
          IsPullback pZ pX ψ f → UniversallyInjective pZ := sorry

namespace existsSchemeSurjectiveOnTarget

/-- A surjective scheme morphism to `Y` with universally injective pullbacks of
`f` witnesses `existsSchemeSurjectiveOnTarget f`. -/
theorem of {Z : Over S} (ψ : ofOver Z ⟶ Y) [Surjective ψ]
    (h : ∀ {P : AlgebraicSpace S} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
      IsPullback pZ pX ψ f → UniversallyInjective pZ) :
    existsSchemeSurjectiveOnTarget f := sorry

/-- `existsSchemeSurjectiveOnTarget f` supplies a surjective scheme morphism to
`Y` along which pullbacks of `f` are universally injective. -/
theorem spec (h : existsSchemeSurjectiveOnTarget f) :
    ∃ (Z : Over S) (ψ : ofOver Z ⟶ Y),
      Surjective ψ ∧
        ∀ {P : AlgebraicSpace S} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
          IsPullback pZ pX ψ f → UniversallyInjective pZ := sorry

end existsSchemeSurjectiveOnTarget

/-- There is a Zariski covering of `Y` along which every inverse-image
projection of `f` is universally injective. -/
def existsZariskiCover : Prop :=
  ∃ (𝒰 : ZariskiCover.{u, u} Y),
    ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → UniversallyInjective pYi

/-- `existsZariskiCover f` is the existence of a Zariski covering of `Y` whose
inverse images under `f` are universally injective over the covering opens. -/
theorem existsZariskiCover_iff : existsZariskiCover f ↔
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i (P : AlgebraicSpace S) (pYi : P ⟶ 𝒰.X i) (pX : P ⟶ X),
        IsPullback pYi pX (𝒰.f i) f → UniversallyInjective pYi := sorry

namespace existsZariskiCover

/-- A Zariski covering of `Y` with universally injective inverse-image
projections of `f` witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → UniversallyInjective pYi) :
    existsZariskiCover f := sorry

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` are universally injective over the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → UniversallyInjective pYi := sorry

end existsZariskiCover

/-- A morphism of algebraic spaces is universally injective if and only if it
is universally injective after every scheme-valued base change, after every
affine-scheme-valued base change, after a surjective scheme morphism to its
target, or over a Zariski covering of its target. -/
theorem tfae_local :
    List.TFAE [UniversallyInjective f, forallScheme f, forallAffine f,
      existsSchemeSurjectiveOnTarget f, existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is universally injective iff every
scheme-valued base change is universally injective. -/
theorem iff_forallScheme : UniversallyInjective f ↔ forallScheme f := (tfae_local f).out 0 1

/-- A morphism of algebraic spaces is universally injective iff every
affine-scheme-valued base change is universally injective. -/
theorem iff_forallAffine : UniversallyInjective f ↔ forallAffine f := (tfae_local f).out 0 2

/-- A morphism of algebraic spaces is universally injective iff some surjective
scheme morphism to the target has universally injective pullback. -/
theorem iff_existsSchemeSurjectiveOnTarget :
    UniversallyInjective f ↔ existsSchemeSurjectiveOnTarget f := (tfae_local f).out 0 3

/-- A morphism of algebraic spaces is universally injective iff some Zariski
covering of the target has universally injective inverse images under `f`. -/
theorem iff_existsZariskiCover :
    UniversallyInjective f ↔ existsZariskiCover f := (tfae_local f).out 0 4

end UniversallyInjective

end AlgebraicGeometry.AlgebraicSpace
