/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-!
# Characterizations of immersions of algebraic spaces

Closed immersions, open immersions, and immersions of algebraic spaces are
tested on scheme-valued base change, étale scheme atlases, and Zariski
coverings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace IsClosedImmersion

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- The base change of `f` along every morphism from a scheme over `S` is a
closed immersion. -/
def forallScheme : Prop :=
  ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → IsClosedImmersion pZ

/-- `forallScheme f` means every scheme-valued pullback projection of `f` is a
closed immersion. -/
theorem forallScheme_iff : forallScheme f ↔
    ∀ (Z : Over S) (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → IsClosedImmersion pZ := by
  constructor
  · intro h Z P g pZ pX sq
    exact h sq
  · intro h Z P g pZ pX sq
    exact h Z P g pZ pX sq

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → IsClosedImmersion pZ) : forallScheme f := h

/-- Under `forallScheme f`, the test-leg of any scheme-valued pullback of `f` is
a closed immersion. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : IsClosedImmersion pZ := h sq

end forallScheme

/-- The base change of `f` along every morphism from an affine scheme over `S`
is a closed immersion. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → IsClosedImmersion pZ

/-- `forallAffine f` means every affine-scheme-valued pullback projection of `f`
is a closed immersion. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → IsClosedImmersion pZ := by
  constructor
  · intro h Z hZ P g pZ pX sq
    exact h sq
  · intro h Z hZ P g pZ pX sq
    exact h Z P g pZ pX sq

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses `forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → IsClosedImmersion pZ) : forallAffine f := h

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is a closed immersion. -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : IsClosedImmersion pZ := h sq

end forallAffine

/-- There is a surjective étale morphism from a scheme to `Y` along which every
pullback of `f` is a closed immersion. -/
def existsEtaleOnTarget : Prop :=
  ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
    Etale ψ ∧ Surjective ψ ∧
      ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
        IsPullback pV pX ψ f → IsClosedImmersion pV

/-- `existsEtaleOnTarget f` is the existence of a surjective étale scheme atlas
of `Y` along which pullbacks of `f` are closed immersions. -/
theorem existsEtaleOnTarget_iff : existsEtaleOnTarget f ↔
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ (P : AlgebraicSpace S) (pV : P ⟶ ofOver V) (pX : P ⟶ X),
          IsPullback pV pX ψ f → IsClosedImmersion pV := by
  constructor
  · rintro ⟨V, ψ, hE, hS, h⟩
    exact ⟨V, ψ, hE, hS, fun P pV pX sq => h sq⟩
  · rintro ⟨V, ψ, hE, hS, h⟩
    exact ⟨V, ψ, hE, hS, fun {P} {pV} {pX} sq => h P pV pX sq⟩

namespace existsEtaleOnTarget

/-- A surjective étale scheme atlas of `Y` with closed-immersion pullbacks of
`f` witnesses `existsEtaleOnTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
      IsPullback pV pX ψ f → IsClosedImmersion pV) : existsEtaleOnTarget f := ⟨V, ψ, inferInstance, inferInstance, h⟩

/-- `existsEtaleOnTarget f` supplies a surjective étale scheme atlas of `Y`
along which pullbacks of `f` are closed immersions. -/
theorem spec (h : existsEtaleOnTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
          IsPullback pV pX ψ f → IsClosedImmersion pV := h

end existsEtaleOnTarget

/-- There is a Zariski covering of `Y` along which every inverse-image
projection of `f` is a closed immersion. -/
def existsZariskiCover : Prop :=
  ∃ (𝒰 : ZariskiCover.{u, u} Y),
    ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → IsClosedImmersion pYi

/-- `existsZariskiCover f` is the existence of a Zariski covering of `Y` whose
inverse images under `f` are closed immersions into the covering opens. -/
theorem existsZariskiCover_iff : existsZariskiCover f ↔
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i (P : AlgebraicSpace S) (pYi : P ⟶ 𝒰.X i) (pX : P ⟶ X),
        IsPullback pYi pX (𝒰.f i) f → IsClosedImmersion pYi := by
  constructor
  · rintro ⟨𝒰, h⟩
    exact ⟨𝒰, fun i P pYi pX sq => h i sq⟩
  · rintro ⟨𝒰, h⟩
    exact ⟨𝒰, fun i {P} {pYi} {pX} sq => h i P pYi pX sq⟩

namespace existsZariskiCover

/-- A Zariski covering of `Y` with closed-immersion inverse-image projections of
`f` witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → IsClosedImmersion pYi) :
    existsZariskiCover f := ⟨𝒰, h⟩

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` are closed immersions into the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → IsClosedImmersion pYi := h

end existsZariskiCover

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`, the following are equivalent: `IsClosedImmersion f`; every
scheme-valued base change of `f` is a closed immersion; every
affine-scheme-valued base change of `f` is a closed immersion; some surjective
étale scheme atlas of `Y` has closed-immersion pullback of `f`; and some
Zariski covering of `Y` has each inverse-image projection `f⁻¹(Yᵢ) ⟶ Yᵢ` a
closed immersion. -/
theorem tfae :
    List.TFAE [IsClosedImmersion f, forallScheme f, forallAffine f, existsEtaleOnTarget f,
      existsZariskiCover f] := by
  sorry

/-- A morphism of algebraic spaces is a closed immersion iff every
scheme-valued base change is a closed immersion. -/
theorem iff_forallScheme : IsClosedImmersion f ↔ forallScheme f := (tfae f).out 0 1

/-- A morphism of algebraic spaces is a closed immersion iff every
affine-scheme-valued base change is a closed immersion. -/
theorem iff_forallAffine : IsClosedImmersion f ↔ forallAffine f := (tfae f).out 0 2

/-- A morphism of algebraic spaces is a closed immersion iff some surjective
étale scheme atlas of the target has closed-immersion pullback. -/
theorem iff_existsEtaleOnTarget : IsClosedImmersion f ↔ existsEtaleOnTarget f := (tfae f).out 0 3

/-- A morphism of algebraic spaces is a closed immersion iff some Zariski
covering of the target has closed-immersion inverse images under `f`. -/
theorem iff_existsZariskiCover : IsClosedImmersion f ↔ existsZariskiCover f := (tfae f).out 0 4


end IsClosedImmersion

namespace IsOpenImmersion

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- The base change of `f` along every morphism from a scheme over `S` is an
open immersion. -/
def forallScheme : Prop :=
  ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → IsOpenImmersion pZ

/-- `forallScheme f` means every scheme-valued pullback projection of `f` is an
open immersion. -/
theorem forallScheme_iff : forallScheme f ↔
    ∀ (Z : Over S) (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → IsOpenImmersion pZ := by
  constructor
  · intro h Z P g pZ pX sq
    exact h sq
  · intro h Z P g pZ pX sq
    exact h Z P g pZ pX sq

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → IsOpenImmersion pZ) : forallScheme f := h

/-- Under `forallScheme f`, the test-leg of any scheme-valued pullback of `f` is
an open immersion. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : IsOpenImmersion pZ := h sq

end forallScheme

/-- The base change of `f` along every morphism from an affine scheme over `S`
is an open immersion. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → IsOpenImmersion pZ

/-- `forallAffine f` means every affine-scheme-valued pullback projection of `f`
is an open immersion. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → IsOpenImmersion pZ := by
  constructor
  · intro h Z hZ P g pZ pX sq
    exact h sq
  · intro h Z hZ P g pZ pX sq
    exact h Z P g pZ pX sq

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses `forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → IsOpenImmersion pZ) : forallAffine f := h

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is an open immersion. -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : IsOpenImmersion pZ := h sq

end forallAffine

/-- There is a surjective étale morphism from a scheme to `Y` along which every
pullback of `f` is an open immersion. -/
def existsEtaleOnTarget : Prop :=
  ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
    Etale ψ ∧ Surjective ψ ∧
      ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
        IsPullback pV pX ψ f → IsOpenImmersion pV

/-- `existsEtaleOnTarget f` is the existence of a surjective étale scheme atlas
of `Y` along which pullbacks of `f` are open immersions. -/
theorem existsEtaleOnTarget_iff : existsEtaleOnTarget f ↔
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ (P : AlgebraicSpace S) (pV : P ⟶ ofOver V) (pX : P ⟶ X),
          IsPullback pV pX ψ f → IsOpenImmersion pV := by
  constructor
  · rintro ⟨V, ψ, hE, hS, h⟩
    exact ⟨V, ψ, hE, hS, fun P pV pX sq => h sq⟩
  · rintro ⟨V, ψ, hE, hS, h⟩
    exact ⟨V, ψ, hE, hS, fun {P} {pV} {pX} sq => h P pV pX sq⟩

namespace existsEtaleOnTarget

/-- A surjective étale scheme atlas of `Y` with open-immersion pullbacks of `f`
witnesses `existsEtaleOnTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
      IsPullback pV pX ψ f → IsOpenImmersion pV) : existsEtaleOnTarget f := ⟨V, ψ, inferInstance, inferInstance, h⟩

/-- `existsEtaleOnTarget f` supplies a surjective étale scheme atlas of `Y`
along which pullbacks of `f` are open immersions. -/
theorem spec (h : existsEtaleOnTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
          IsPullback pV pX ψ f → IsOpenImmersion pV := h

end existsEtaleOnTarget

/-- There is a Zariski covering of `Y` along which every inverse-image
projection of `f` is an open immersion. -/
def existsZariskiCover : Prop :=
  ∃ (𝒰 : ZariskiCover.{u, u} Y),
    ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → IsOpenImmersion pYi

/-- `existsZariskiCover f` is the existence of a Zariski covering of `Y` whose
inverse images under `f` are open immersions into the covering opens. -/
theorem existsZariskiCover_iff : existsZariskiCover f ↔
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i (P : AlgebraicSpace S) (pYi : P ⟶ 𝒰.X i) (pX : P ⟶ X),
        IsPullback pYi pX (𝒰.f i) f → IsOpenImmersion pYi := by
  constructor
  · rintro ⟨𝒰, h⟩
    exact ⟨𝒰, fun i P pYi pX sq => h i sq⟩
  · rintro ⟨𝒰, h⟩
    exact ⟨𝒰, fun i {P} {pYi} {pX} sq => h i P pYi pX sq⟩

namespace existsZariskiCover

/-- A Zariski covering of `Y` with open-immersion inverse-image projections of
`f` witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → IsOpenImmersion pYi) :
    existsZariskiCover f := ⟨𝒰, h⟩

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` are open immersions into the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → IsOpenImmersion pYi := h

end existsZariskiCover

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`, the following are equivalent: `IsOpenImmersion f`; every
scheme-valued base change of `f` is an open immersion; every
affine-scheme-valued base change of `f` is an open immersion; some surjective
étale scheme atlas of `Y` has open-immersion pullback of `f`; and some Zariski
covering of `Y` has each inverse-image projection `f⁻¹(Yᵢ) ⟶ Yᵢ` an open
immersion. -/
theorem tfae :
    List.TFAE [IsOpenImmersion f, forallScheme f, forallAffine f, existsEtaleOnTarget f,
      existsZariskiCover f] := by
  sorry

/-- A morphism of algebraic spaces is an open immersion iff every scheme-valued
base change is an open immersion. -/
theorem iff_forallScheme : IsOpenImmersion f ↔ forallScheme f := (tfae f).out 0 1

/-- A morphism of algebraic spaces is an open immersion iff every
affine-scheme-valued base change is an open immersion. -/
theorem iff_forallAffine : IsOpenImmersion f ↔ forallAffine f := (tfae f).out 0 2

/-- A morphism of algebraic spaces is an open immersion iff some surjective
étale scheme atlas of the target has open-immersion pullback. -/
theorem iff_existsEtaleOnTarget : IsOpenImmersion f ↔ existsEtaleOnTarget f := (tfae f).out 0 3

/-- A morphism of algebraic spaces is an open immersion iff some Zariski
covering of the target has open-immersion inverse images under `f`. -/
theorem iff_existsZariskiCover : IsOpenImmersion f ↔ existsZariskiCover f := (tfae f).out 0 4


end IsOpenImmersion

namespace IsImmersion

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- The base change of `f` along every morphism from a scheme over `S` is an
immersion. -/
def forallScheme : Prop :=
  ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → IsImmersion pZ

/-- `forallScheme f` means every scheme-valued pullback projection of `f` is an
immersion. -/
theorem forallScheme_iff : forallScheme f ↔
    ∀ (Z : Over S) (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → IsImmersion pZ := by
  constructor
  · intro h Z P g pZ pX sq
    exact h sq
  · intro h Z P g pZ pX sq
    exact h Z P g pZ pX sq

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → IsImmersion pZ) : forallScheme f := h

/-- Under `forallScheme f`, the test-leg of any scheme-valued pullback of `f` is
an immersion. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : IsImmersion pZ := h sq

end forallScheme

/-- The base change of `f` along every morphism from an affine scheme over `S`
is an immersion. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → IsImmersion pZ

/-- `forallAffine f` means every affine-scheme-valued pullback projection of `f`
is an immersion. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → IsImmersion pZ := by
  constructor
  · intro h Z hZ P g pZ pX sq
    exact h sq
  · intro h Z hZ P g pZ pX sq
    exact h Z P g pZ pX sq

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses `forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → IsImmersion pZ) : forallAffine f := h

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is an immersion. -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : IsImmersion pZ := h sq

end forallAffine

/-- There is a surjective étale morphism from a scheme to `Y` along which every
pullback of `f` is an immersion. -/
def existsEtaleOnTarget : Prop :=
  ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
    Etale ψ ∧ Surjective ψ ∧
      ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
        IsPullback pV pX ψ f → IsImmersion pV

/-- `existsEtaleOnTarget f` is the existence of a surjective étale scheme atlas
of `Y` along which pullbacks of `f` are immersions. -/
theorem existsEtaleOnTarget_iff : existsEtaleOnTarget f ↔
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ (P : AlgebraicSpace S) (pV : P ⟶ ofOver V) (pX : P ⟶ X),
          IsPullback pV pX ψ f → IsImmersion pV := by
  constructor
  · rintro ⟨V, ψ, hE, hS, h⟩
    exact ⟨V, ψ, hE, hS, fun P pV pX sq => h sq⟩
  · rintro ⟨V, ψ, hE, hS, h⟩
    exact ⟨V, ψ, hE, hS, fun {P} {pV} {pX} sq => h P pV pX sq⟩

namespace existsEtaleOnTarget

/-- A surjective étale scheme atlas of `Y` with immersion pullbacks of `f`
witnesses `existsEtaleOnTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
      IsPullback pV pX ψ f → IsImmersion pV) : existsEtaleOnTarget f := ⟨V, ψ, inferInstance, inferInstance, h⟩

/-- `existsEtaleOnTarget f` supplies a surjective étale scheme atlas of `Y`
along which pullbacks of `f` are immersions. -/
theorem spec (h : existsEtaleOnTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
          IsPullback pV pX ψ f → IsImmersion pV := h

end existsEtaleOnTarget

/-- There is a Zariski covering of `Y` along which every inverse-image
projection of `f` is an immersion. -/
def existsZariskiCover : Prop :=
  ∃ (𝒰 : ZariskiCover.{u, u} Y),
    ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → IsImmersion pYi

/-- `existsZariskiCover f` is the existence of a Zariski covering of `Y` whose
inverse images under `f` are immersions into the covering opens. -/
theorem existsZariskiCover_iff : existsZariskiCover f ↔
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i (P : AlgebraicSpace S) (pYi : P ⟶ 𝒰.X i) (pX : P ⟶ X),
        IsPullback pYi pX (𝒰.f i) f → IsImmersion pYi := by
  constructor
  · rintro ⟨𝒰, h⟩
    exact ⟨𝒰, fun i P pYi pX sq => h i sq⟩
  · rintro ⟨𝒰, h⟩
    exact ⟨𝒰, fun i {P} {pYi} {pX} sq => h i P pYi pX sq⟩

namespace existsZariskiCover

/-- A Zariski covering of `Y` with immersion inverse-image projections of `f`
witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → IsImmersion pYi) :
    existsZariskiCover f := ⟨𝒰, h⟩

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` are immersions into the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → IsImmersion pYi := h

end existsZariskiCover

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`, the following are equivalent: `IsImmersion f`; every scheme-valued
base change of `f` is an immersion; every affine-scheme-valued base change of
`f` is an immersion; some surjective étale scheme atlas of `Y` has immersion
pullback of `f`; and some Zariski covering of `Y` has each inverse-image
projection `f⁻¹(Yᵢ) ⟶ Yᵢ` an immersion. -/
theorem tfae :
    List.TFAE [IsImmersion f, forallScheme f, forallAffine f, existsEtaleOnTarget f,
      existsZariskiCover f] := by
  sorry

/-- A morphism of algebraic spaces is an immersion iff every scheme-valued base
change is an immersion. -/
theorem iff_forallScheme : IsImmersion f ↔ forallScheme f := (tfae f).out 0 1

/-- A morphism of algebraic spaces is an immersion iff every
affine-scheme-valued base change is an immersion. -/
theorem iff_forallAffine : IsImmersion f ↔ forallAffine f := (tfae f).out 0 2

/-- A morphism of algebraic spaces is an immersion iff some surjective étale
scheme atlas of the target has immersion pullback. -/
theorem iff_existsEtaleOnTarget : IsImmersion f ↔ existsEtaleOnTarget f := (tfae f).out 0 3

/-- A morphism of algebraic spaces is an immersion iff some Zariski covering of
the target has immersion inverse images under `f`. -/
theorem iff_existsZariskiCover : IsImmersion f ↔ existsZariskiCover f := (tfae f).out 0 4


end IsImmersion

end AlgebraicGeometry.AlgebraicSpace
