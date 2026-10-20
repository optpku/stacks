/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyClosed
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic

/-!
# Local tests for universally closed morphisms of algebraic spaces

Universally closed morphisms of algebraic spaces may be tested on scheme-valued
and affine base change by closed projections, on a surjective étale scheme atlas
of the target, and on a Zariski covering of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Closed

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- The projection of every scheme-valued base change of `f` is a closed map on
points. -/
def forallScheme : Prop :=
  ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Closed pZ

/-- `forallScheme f` means every scheme-valued pullback projection of `f` is a
closed morphism. -/
theorem forallScheme_iff : forallScheme f ↔
    ∀ (Z : Over S) (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → Closed pZ := by
  constructor
  · intro h Z P g pZ pX sq
    exact h sq
  · intro h Z P g pZ pX sq
    exact h Z P g pZ pX sq

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Closed pZ) : forallScheme f := h

/-- Under `forallScheme f`, the test-leg of any scheme-valued pullback of `f` is
closed. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Closed pZ := h sq

end forallScheme

/-- The projection of every affine-scheme-valued base change of `f` is a closed
map on points. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Closed pZ

/-- `forallAffine f` means every affine-scheme-valued pullback projection of `f`
is a closed morphism. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → Closed pZ := by
  constructor
  · intro h Z hZ P g pZ pX sq
    exact h sq
  · intro h Z hZ P g pZ pX sq
    exact h Z P g pZ pX sq

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses
`forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Closed pZ) : forallAffine f := h

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is closed. -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Closed pZ := h sq

end forallAffine

end Closed

namespace UniversallyClosed

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- There is a surjective étale morphism from a scheme to `Y` along which every
pullback of `f` is universally closed. -/
def existsEtaleOnTarget : Prop :=
  ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
    Etale ψ ∧ Surjective ψ ∧
      ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
        IsPullback pV pX ψ f → UniversallyClosed pV

/-- `existsEtaleOnTarget f` is the existence of a surjective étale scheme atlas
of `Y` along which pullbacks of `f` are universally closed. -/
theorem existsEtaleOnTarget_iff : existsEtaleOnTarget f ↔
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ (P : AlgebraicSpace S) (pV : P ⟶ ofOver V) (pX : P ⟶ X),
          IsPullback pV pX ψ f → UniversallyClosed pV := by
  constructor
  · rintro ⟨V, ψ, hE, hS, h⟩
    exact ⟨V, ψ, hE, hS, fun P pV pX sq => h sq⟩
  · rintro ⟨V, ψ, hE, hS, h⟩
    exact ⟨V, ψ, hE, hS, fun {P} {pV} {pX} sq => h P pV pX sq⟩

namespace existsEtaleOnTarget

/-- A surjective étale scheme atlas of `Y` with universally closed pullbacks of
`f` witnesses `existsEtaleOnTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
      IsPullback pV pX ψ f → UniversallyClosed pV) :
    existsEtaleOnTarget f := ⟨V, ψ, inferInstance, inferInstance, h⟩

/-- `existsEtaleOnTarget f` supplies a surjective étale scheme atlas of `Y`
along which pullbacks of `f` are universally closed. -/
theorem spec (h : existsEtaleOnTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
          IsPullback pV pX ψ f → UniversallyClosed pV := h

end existsEtaleOnTarget

/-- There is a Zariski covering of `Y` along which every inverse-image
projection of `f` is universally closed. -/
def existsZariskiCover : Prop :=
  ∃ (𝒰 : ZariskiCover.{u, u} Y),
    ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → UniversallyClosed pYi

/-- `existsZariskiCover f` is the existence of a Zariski covering of `Y` whose
inverse images under `f` are universally closed over the covering opens. -/
theorem existsZariskiCover_iff : existsZariskiCover f ↔
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i (P : AlgebraicSpace S) (pYi : P ⟶ 𝒰.X i) (pX : P ⟶ X),
        IsPullback pYi pX (𝒰.f i) f → UniversallyClosed pYi := by
  constructor
  · rintro ⟨𝒰, h⟩
    exact ⟨𝒰, fun i P pYi pX sq => h i sq⟩
  · rintro ⟨𝒰, h⟩
    exact ⟨𝒰, fun i {P} {pYi} {pX} sq => h i P pYi pX sq⟩

namespace existsZariskiCover

/-- A Zariski covering of `Y` with universally closed inverse-image projections
of `f` witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → UniversallyClosed pYi) :
    existsZariskiCover f := ⟨𝒰, h⟩

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` are universally closed over the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → UniversallyClosed pYi := h

end existsZariskiCover

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the following are equivalent: `UniversallyClosed f`; every scheme-valued
base change of `f` has closed projection on points; every affine-scheme-valued
base change of `f` has closed projection on points; some surjective étale
scheme atlas of `Y` has universally closed pullback of `f`; and some Zariski
covering of `Y` has each inverse-image projection `f⁻¹(Yᵢ) ⟶ Yᵢ` universally
closed. -/
theorem tfae :
    List.TFAE [UniversallyClosed f, Closed.forallScheme f, Closed.forallAffine f,
      existsEtaleOnTarget f, existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is universally closed iff every
scheme-valued base change has closed projection on points. -/
theorem iff_forallScheme : UniversallyClosed f ↔ Closed.forallScheme f := (tfae f).out 0 1

/-- A morphism of algebraic spaces is universally closed iff every
affine-scheme-valued base change has closed projection on points. -/
theorem iff_forallAffine : UniversallyClosed f ↔ Closed.forallAffine f := (tfae f).out 0 2

/-- A morphism of algebraic spaces is universally closed iff some surjective
étale scheme atlas of the target has universally closed pullback. -/
theorem iff_existsEtaleOnTarget :
    UniversallyClosed f ↔ existsEtaleOnTarget f := (tfae f).out 0 3

/-- A morphism of algebraic spaces is universally closed iff some Zariski
covering of the target has universally closed inverse images under `f`. -/
theorem iff_existsZariskiCover :
    UniversallyClosed f ↔ existsZariskiCover f := (tfae f).out 0 4

end UniversallyClosed

end AlgebraicGeometry.AlgebraicSpace
