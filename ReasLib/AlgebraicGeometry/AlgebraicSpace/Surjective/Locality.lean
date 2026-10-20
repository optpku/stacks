/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Characterizations of surjective morphisms of algebraic spaces

Surjectivity of a morphism of algebraic spaces is tested on scheme-valued base
change, étale scheme atlases, and Zariski coverings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Surjective

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- Surjectivity after every base change along a morphism from a scheme over `S`. -/
def forallScheme : Prop :=
  ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Surjective pZ

/-- `forallScheme f` means every scheme-valued pullback projection of `f` is
surjective. -/
theorem forallScheme_iff : forallScheme f ↔
    ∀ (Z : Over S) (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → Surjective pZ := by
  constructor
  · intro h Z P g pZ pX sq
    exact h sq
  · intro h Z P g pZ pX sq
    exact h Z P g pZ pX sq

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Surjective pZ) : forallScheme f := h

/-- Under `forallScheme f`, the test-leg of any scheme-valued pullback of `f` is
surjective. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Surjective pZ := h sq

end forallScheme

/-- Surjectivity after every base change along a morphism from an affine scheme
over `S`. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Surjective pZ

/-- `forallAffine f` means every affine-scheme-valued pullback projection of `f`
is surjective. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → Surjective pZ := by
  constructor
  · intro h Z hZ P g pZ pX sq
    exact h sq
  · intro h Z hZ P g pZ pX sq
    exact h Z P g pZ pX sq

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses `forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Surjective pZ) : forallAffine f := h

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is surjective. -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Surjective pZ := h sq

end forallAffine

/-- There is a surjective étale morphism from a scheme to `Y` along which every
pullback of `f` is surjective. -/
def existsEtaleOnTarget : Prop :=
  ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
    Etale ψ ∧ Surjective ψ ∧
      ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
        IsPullback pV pX ψ f → Surjective pV

/-- `existsEtaleOnTarget f` is the existence of a surjective étale scheme atlas
of `Y` along which pullbacks of `f` are surjective. -/
theorem existsEtaleOnTarget_iff : existsEtaleOnTarget f ↔
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ (P : AlgebraicSpace S) (pV : P ⟶ ofOver V) (pX : P ⟶ X),
          IsPullback pV pX ψ f → Surjective pV := by
  constructor
  · rintro ⟨V, ψ, hEtale, hSurj, h⟩
    exact ⟨V, ψ, hEtale, hSurj, fun P pV pX sq ↦ h sq⟩
  · rintro ⟨V, ψ, hEtale, hSurj, h⟩
    exact ⟨V, ψ, hEtale, hSurj, fun {P} {pV} {pX} sq ↦ h P pV pX sq⟩

namespace existsEtaleOnTarget

/-- A surjective étale scheme atlas of `Y` with surjective pullbacks of `f`
witnesses `existsEtaleOnTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
      IsPullback pV pX ψ f → Surjective pV) : existsEtaleOnTarget f := ⟨V, ψ, inferInstance, inferInstance, h⟩

/-- `existsEtaleOnTarget f` supplies a surjective étale scheme atlas of `Y`
along which pullbacks of `f` are surjective. -/
theorem spec (h : existsEtaleOnTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
          IsPullback pV pX ψ f → Surjective pV := h

end existsEtaleOnTarget

/-- There is a surjective étale morphism from a scheme to `X` whose composite
with `f` is surjective. -/
def existsEtaleOnSource : Prop :=
  ∃ (U : Over S) (φ : ofOver U ⟶ X), Etale φ ∧ Surjective φ ∧ Surjective (φ ≫ f)

/-- `existsEtaleOnSource f` is the existence of a surjective étale scheme atlas
of `X` whose composite with `f` is surjective. -/
theorem existsEtaleOnSource_iff : existsEtaleOnSource f ↔
    ∃ (U : Over S) (φ : ofOver U ⟶ X),
      Etale φ ∧ Surjective φ ∧ Surjective (φ ≫ f) := Iff.rfl

namespace existsEtaleOnSource

/-- A surjective étale scheme atlas of `X` with surjective composite with `f`
witnesses `existsEtaleOnSource f`. -/
theorem of {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] [Surjective φ]
    (h : Surjective (φ ≫ f)) : existsEtaleOnSource f := ⟨U, φ, inferInstance, inferInstance, h⟩

/-- `existsEtaleOnSource f` supplies a surjective étale scheme atlas of `X`
whose composite with `f` is surjective. -/
theorem spec (h : existsEtaleOnSource f) :
    ∃ (U : Over S) (φ : ofOver U ⟶ X),
      Etale φ ∧ Surjective φ ∧ Surjective (φ ≫ f) := h

end existsEtaleOnSource

/-- There is a commutative square of surjective étale scheme atlases over `f`
with surjective top arrow. -/
def existsEtaleSquare : Prop :=
  ∃ (U V : Over S) (φ : ofOver U ⟶ X) (ψ : ofOver V ⟶ Y) (h : ofOver U ⟶ ofOver V),
    CommSq h φ ψ f ∧ Etale φ ∧ Surjective φ ∧ Etale ψ ∧ Surjective ψ ∧ Surjective h

/-- `existsEtaleSquare f` is the existence of a commutative square of surjective
étale scheme atlases over `f` with surjective top arrow. -/
theorem existsEtaleSquare_iff : existsEtaleSquare f ↔
    ∃ (U V : Over S) (φ : ofOver U ⟶ X) (ψ : ofOver V ⟶ Y)
      (h : ofOver U ⟶ ofOver V),
      CommSq h φ ψ f ∧ Etale φ ∧ Surjective φ ∧ Etale ψ ∧ Surjective ψ ∧
        Surjective h := Iff.rfl

namespace existsEtaleSquare

/-- A commutative square of surjective étale scheme atlases with surjective top
arrow witnesses `existsEtaleSquare f`. -/
theorem of {U V : Over S} {φ : ofOver U ⟶ X} {ψ : ofOver V ⟶ Y}
    {h : ofOver U ⟶ ofOver V} (sq : CommSq h φ ψ f)
    [Etale φ] [Surjective φ] [Etale ψ] [Surjective ψ] [Surjective h] :
    existsEtaleSquare f := ⟨U, V, φ, ψ, h, sq, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩

/-- `existsEtaleSquare f` supplies a commutative square of surjective étale
scheme atlases over `f` with surjective top arrow. -/
theorem spec (h : existsEtaleSquare f) :
    ∃ (U V : Over S) (φ : ofOver U ⟶ X) (ψ : ofOver V ⟶ Y)
      (h : ofOver U ⟶ ofOver V),
      CommSq h φ ψ f ∧ Etale φ ∧ Surjective φ ∧ Etale ψ ∧ Surjective ψ ∧
        Surjective h := h

end existsEtaleSquare

/-- There is a Zariski covering of `Y` along which every inverse-image
projection of `f` is surjective. -/
def existsZariskiCover : Prop :=
  ∃ (𝒰 : ZariskiCover.{u, u} Y),
    ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → Surjective pYi

/-- `existsZariskiCover f` is the existence of a Zariski covering of `Y` whose
inverse images under `f` map surjectively to the covering opens. -/
theorem existsZariskiCover_iff : existsZariskiCover f ↔
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i (P : AlgebraicSpace S) (pYi : P ⟶ 𝒰.X i) (pX : P ⟶ X),
        IsPullback pYi pX (𝒰.f i) f → Surjective pYi := by
  constructor
  · rintro ⟨𝒰, h⟩
    exact ⟨𝒰, fun i P pYi pX sq ↦ h i sq⟩
  · rintro ⟨𝒰, h⟩
    exact ⟨𝒰, fun i {P} {pYi} {pX} sq ↦ h i P pYi pX sq⟩

namespace existsZariskiCover

/-- A Zariski covering of `Y` with surjective inverse-image projections of `f`
witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → Surjective pYi) :
    existsZariskiCover f := ⟨𝒰, h⟩

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` map surjectively to the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → Surjective pYi := h

end existsZariskiCover

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the following are equivalent: `Surjective f`; every scheme-valued base
change of `f` is surjective; every affine-scheme-valued base change of `f` is
surjective; some surjective étale scheme atlas of `Y` has surjective pullback of
`f`; some surjective étale scheme atlas of `X` has surjective composite with
`f`; some commutative square of surjective étale scheme atlases over `f` has
surjective top arrow; and some Zariski covering of `Y` has each inverse image
under `f` surjective. -/
theorem tfae :
    List.TFAE [Surjective f, forallScheme f, forallAffine f, existsEtaleOnTarget f,
      existsEtaleOnSource f, existsEtaleSquare f, existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is surjective iff every scheme-valued base
change is surjective. -/
theorem iff_forallScheme : Surjective f ↔ forallScheme f :=
  (tfae f).out 0 1

/-- A morphism of algebraic spaces is surjective iff every affine-scheme-valued
base change is surjective. -/
theorem iff_forallAffine : Surjective f ↔ forallAffine f :=
  (tfae f).out 0 2

/-- A morphism of algebraic spaces is surjective iff some surjective étale
scheme atlas of the target has surjective pullback. -/
theorem iff_existsEtaleOnTarget : Surjective f ↔ existsEtaleOnTarget f :=
  (tfae f).out 0 3

/-- A morphism of algebraic spaces is surjective iff some surjective étale
scheme atlas of the source has surjective composite with `f`. -/
theorem iff_existsEtaleOnSource : Surjective f ↔ existsEtaleOnSource f :=
  (tfae f).out 0 4

/-- A morphism of algebraic spaces is surjective iff some commutative square of
surjective étale scheme atlases has surjective top arrow. -/
theorem iff_existsEtaleSquare : Surjective f ↔ existsEtaleSquare f :=
  (tfae f).out 0 5

/-- A morphism of algebraic spaces is surjective iff some Zariski covering of
the target has surjective inverse images under `f`. -/
theorem iff_existsZariskiCover : Surjective f ↔ existsZariskiCover f :=
  (tfae f).out 0 6

/-- The pullback projection to a scheme is surjective whenever the morphism
being pulled back is surjective. -/
instance pullback_snd_ofOver {Z : Over S} [Surjective f] (g : ofOver Z ⟶ Y)
    [HasPullback f g] : Surjective (pullback.snd f g) :=
  forallScheme.spec f ((iff_forallScheme f).mp inferInstance)
    (IsPullback.of_hasPullback f g).flip

end Surjective

end AlgebraicGeometry.AlgebraicSpace
