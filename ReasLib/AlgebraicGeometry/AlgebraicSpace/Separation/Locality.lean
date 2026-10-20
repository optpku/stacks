/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-!
# Local tests for separation axioms of morphisms of algebraic spaces

Separatedness, local separatedness, and quasi-separatedness of a morphism of
algebraic spaces are tested on scheme-valued and affine base change, on the
absolute separation property of affine pullbacks, on étale scheme atlases, and
on Zariski coverings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Separated

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- The base change of `f` along every morphism from a scheme over `S` is
separated. -/
def forallScheme : Prop :=
  ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Separated pZ

/-- `forallScheme f` means every scheme-valued pullback projection of `f` is
separated. -/
theorem forallScheme_iff : forallScheme f ↔
    ∀ (Z : Over S) (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → Separated pZ := by
  constructor
  · intro h Z P g pZ pX sq
    exact h sq
  · intro h Z P g pZ pX sq
    exact h Z P g pZ pX sq

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Separated pZ) : forallScheme f := by
  exact h

/-- Under `forallScheme f`, the test-leg of any scheme-valued pullback of `f` is
separated. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Separated pZ := by
  exact h sq

/-- The chosen pullback projection `pullback.snd f g` along a morphism from a
scheme is separated whenever `forallScheme f` holds. -/
theorem pullback_snd {Z : Over S} (h : forallScheme f) (g : ofOver Z ⟶ Y)
    [HasPullback f g] : Separated (pullback.snd f g) := by
  exact h (IsPullback.of_hasPullback f g).flip

end forallScheme

/-- The base change of `f` along every morphism from an affine scheme over `S`
is separated. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Separated pZ

/-- `forallAffine f` means every affine-scheme-valued pullback projection of `f`
is separated. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → Separated pZ := by
  constructor
  · intro h Z hZ P g pZ pX sq
    exact h sq
  · intro h Z hZ P g pZ pX sq
    exact h Z P g pZ pX sq

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses `forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Separated pZ) : forallAffine f := by
  exact h

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is separated. -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Separated pZ := by
  exact h sq

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme is separated whenever `forallAffine f` holds. -/
theorem pullback_snd {Z : Over S} [IsAffine Z.left] (h : forallAffine f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] : Separated (pullback.snd f g) := by
  exact h (IsPullback.of_hasPullback f g).flip

end forallAffine

/-- For every affine scheme over `S` mapping to `Y`, the pullback algebraic
space is absolutely separated. -/
def forallAffineSpace : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → IsAbsolutelySeparated P

/-- `forallAffineSpace f` means every affine-scheme-valued pullback object of
`f` is absolutely separated. -/
theorem forallAffineSpace_iff : forallAffineSpace f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → IsAbsolutelySeparated P := by
  constructor
  · intro h Z hZ P g pZ pX sq
    exact h sq
  · intro h Z hZ P g pZ pX sq
    exact h Z P g pZ pX sq

namespace forallAffineSpace

/-- A universal affine-scheme-valued pullback-object condition witnesses
`forallAffineSpace f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → IsAbsolutelySeparated P) : forallAffineSpace f := by
  exact h

/-- Under `forallAffineSpace f`, any affine-scheme-valued pullback object of `f`
is absolutely separated. -/
theorem spec (h : forallAffineSpace f) {Z : Over S} [IsAffine Z.left]
    {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : IsAbsolutelySeparated P := by
  exact h sq

/-- The chosen pullback object `pullback f g` along a morphism from an affine
scheme is absolutely separated whenever `forallAffineSpace f` holds. -/
theorem pullback_snd {Z : Over S} [IsAffine Z.left] (h : forallAffineSpace f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] : IsAbsolutelySeparated (pullback f g) := by
  exact h (IsPullback.of_hasPullback f g).flip

end forallAffineSpace

/-- There is a surjective étale morphism from a scheme to `Y` along which every
pullback of `f` is separated. -/
def existsEtaleOnTarget : Prop :=
  ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
    Etale ψ ∧ Surjective ψ ∧
      ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
        IsPullback pV pX ψ f → Separated pV

/-- `existsEtaleOnTarget f` is the existence of a surjective étale scheme atlas
of `Y` along which pullbacks of `f` are separated. -/
theorem existsEtaleOnTarget_iff : existsEtaleOnTarget f ↔
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ (P : AlgebraicSpace S) (pV : P ⟶ ofOver V) (pX : P ⟶ X),
          IsPullback pV pX ψ f → Separated pV := by
  constructor
  · rintro ⟨V, ψ, he, hs, h⟩
    exact ⟨V, ψ, he, hs, fun P pV pX sq => h sq⟩
  · rintro ⟨V, ψ, he, hs, h⟩
    refine ⟨V, ψ, he, hs, ?_⟩
    intro P pV pX sq
    exact h P pV pX sq

namespace existsEtaleOnTarget

/-- A surjective étale scheme atlas of `Y` with separated pullbacks of `f`
witnesses `existsEtaleOnTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
      IsPullback pV pX ψ f → Separated pV) : existsEtaleOnTarget f := by
  exact ⟨V, ψ, inferInstance, inferInstance, h⟩

/-- `existsEtaleOnTarget f` supplies a surjective étale scheme atlas of `Y`
along which pullbacks of `f` are separated. -/
theorem spec (h : existsEtaleOnTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
          IsPullback pV pX ψ f → Separated pV := by
  exact h

end existsEtaleOnTarget

/-- There is a Zariski covering of `Y` along which every inverse-image
projection of `f` is separated. -/
def existsZariskiCover : Prop :=
  ∃ (𝒰 : ZariskiCover.{u, u} Y),
    ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → Separated pYi

/-- `existsZariskiCover f` is the existence of a Zariski covering of `Y` whose
inverse images under `f` map separately to the covering opens. -/
theorem existsZariskiCover_iff : existsZariskiCover f ↔
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i (P : AlgebraicSpace S) (pYi : P ⟶ 𝒰.X i) (pX : P ⟶ X),
        IsPullback pYi pX (𝒰.f i) f → Separated pYi := by
  constructor
  · rintro ⟨𝒰, h⟩
    exact ⟨𝒰, fun i P pYi pX sq => h i sq⟩
  · rintro ⟨𝒰, h⟩
    refine ⟨𝒰, ?_⟩
    intro i P pYi pX sq
    exact h i P pYi pX sq

namespace existsZariskiCover

/-- A Zariski covering of `Y` with separated inverse-image projections of `f`
witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → Separated pYi) :
    existsZariskiCover f := by
  exact ⟨𝒰, h⟩

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` map separately to the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → Separated pYi := by
  exact h

end existsZariskiCover

end Separated

namespace LocallySeparated

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- The base change of `f` along every morphism from a scheme over `S` is
locally separated. -/
def forallScheme : Prop :=
  ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → LocallySeparated pZ

/-- `forallScheme f` means every scheme-valued pullback projection of `f` is
locally separated. -/
theorem forallScheme_iff : forallScheme f ↔
    ∀ (Z : Over S) (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → LocallySeparated pZ := by
  constructor
  · intro h Z P g pZ pX sq
    exact h sq
  · intro h Z P g pZ pX sq
    exact h Z P g pZ pX sq

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → LocallySeparated pZ) : forallScheme f := by
  exact h

/-- Under `forallScheme f`, the test-leg of any scheme-valued pullback of `f` is
locally separated. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : LocallySeparated pZ := by
  exact h sq

/-- The chosen pullback projection `pullback.snd f g` along a morphism from a
scheme is locally separated whenever `forallScheme f` holds. -/
theorem pullback_snd {Z : Over S} (h : forallScheme f) (g : ofOver Z ⟶ Y)
    [HasPullback f g] : LocallySeparated (pullback.snd f g) := by
  exact h (IsPullback.of_hasPullback f g).flip

end forallScheme

/-- The base change of `f` along every morphism from an affine scheme over `S`
is locally separated. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → LocallySeparated pZ

/-- `forallAffine f` means every affine-scheme-valued pullback projection of `f`
is locally separated. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → LocallySeparated pZ := by
  constructor
  · intro h Z hZ P g pZ pX sq
    exact h sq
  · intro h Z hZ P g pZ pX sq
    exact h Z P g pZ pX sq

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses `forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → LocallySeparated pZ) : forallAffine f := by
  exact h

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is locally separated. -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : LocallySeparated pZ := by
  exact h sq

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme is locally separated whenever `forallAffine f` holds. -/
theorem pullback_snd {Z : Over S} [IsAffine Z.left] (h : forallAffine f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] : LocallySeparated (pullback.snd f g) := by
  exact h (IsPullback.of_hasPullback f g).flip

end forallAffine

/-- For every affine scheme over `S` mapping to `Y`, the pullback algebraic
space is absolutely locally separated. -/
def forallAffineSpace : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → IsAbsolutelyLocallySeparated P

/-- `forallAffineSpace f` means every affine-scheme-valued pullback object of
`f` is absolutely locally separated. -/
theorem forallAffineSpace_iff : forallAffineSpace f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → IsAbsolutelyLocallySeparated P := by
  constructor
  · intro h Z hZ P g pZ pX sq
    exact h sq
  · intro h Z hZ P g pZ pX sq
    exact h Z P g pZ pX sq

namespace forallAffineSpace

/-- A universal affine-scheme-valued pullback-object condition witnesses
`forallAffineSpace f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → IsAbsolutelyLocallySeparated P) :
    forallAffineSpace f := by
  exact h

/-- Under `forallAffineSpace f`, any affine-scheme-valued pullback object of `f`
is absolutely locally separated. -/
theorem spec (h : forallAffineSpace f) {Z : Over S} [IsAffine Z.left]
    {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : IsAbsolutelyLocallySeparated P := by
  exact h sq

/-- The chosen pullback object `pullback f g` along a morphism from an affine
scheme is absolutely locally separated whenever `forallAffineSpace f` holds. -/
theorem pullback_snd {Z : Over S} [IsAffine Z.left] (h : forallAffineSpace f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] :
    IsAbsolutelyLocallySeparated (pullback f g) := by
  exact h (IsPullback.of_hasPullback f g).flip

end forallAffineSpace

/-- There is a surjective étale morphism from a scheme to `Y` along which every
pullback of `f` is locally separated. -/
def existsEtaleOnTarget : Prop :=
  ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
    Etale ψ ∧ Surjective ψ ∧
      ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
        IsPullback pV pX ψ f → LocallySeparated pV

/-- `existsEtaleOnTarget f` is the existence of a surjective étale scheme atlas
of `Y` along which pullbacks of `f` are locally separated. -/
theorem existsEtaleOnTarget_iff : existsEtaleOnTarget f ↔
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ (P : AlgebraicSpace S) (pV : P ⟶ ofOver V) (pX : P ⟶ X),
          IsPullback pV pX ψ f → LocallySeparated pV := by
  constructor
  · rintro ⟨V, ψ, he, hs, h⟩
    exact ⟨V, ψ, he, hs, fun P pV pX sq => h sq⟩
  · rintro ⟨V, ψ, he, hs, h⟩
    refine ⟨V, ψ, he, hs, ?_⟩
    intro P pV pX sq
    exact h P pV pX sq

namespace existsEtaleOnTarget

/-- A surjective étale scheme atlas of `Y` with locally separated pullbacks of
`f` witnesses `existsEtaleOnTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
      IsPullback pV pX ψ f → LocallySeparated pV) : existsEtaleOnTarget f := by
  exact ⟨V, ψ, inferInstance, inferInstance, h⟩

/-- `existsEtaleOnTarget f` supplies a surjective étale scheme atlas of `Y`
along which pullbacks of `f` are locally separated. -/
theorem spec (h : existsEtaleOnTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
          IsPullback pV pX ψ f → LocallySeparated pV := by
  exact h

end existsEtaleOnTarget

/-- There is a Zariski covering of `Y` along which every inverse-image
projection of `f` is locally separated. -/
def existsZariskiCover : Prop :=
  ∃ (𝒰 : ZariskiCover.{u, u} Y),
    ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → LocallySeparated pYi

/-- `existsZariskiCover f` is the existence of a Zariski covering of `Y` whose
inverse images under `f` map locally separately to the covering opens. -/
theorem existsZariskiCover_iff : existsZariskiCover f ↔
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i (P : AlgebraicSpace S) (pYi : P ⟶ 𝒰.X i) (pX : P ⟶ X),
        IsPullback pYi pX (𝒰.f i) f → LocallySeparated pYi := by
  constructor
  · rintro ⟨𝒰, h⟩
    exact ⟨𝒰, fun i P pYi pX sq => h i sq⟩
  · rintro ⟨𝒰, h⟩
    refine ⟨𝒰, ?_⟩
    intro i P pYi pX sq
    exact h i P pYi pX sq

namespace existsZariskiCover

/-- A Zariski covering of `Y` with locally separated inverse-image projections
of `f` witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → LocallySeparated pYi) :
    existsZariskiCover f := by
  exact ⟨𝒰, h⟩

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` map locally separately to the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → LocallySeparated pYi := by
  exact h

end existsZariskiCover

end LocallySeparated

namespace QuasiSeparated

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- The base change of `f` along every morphism from a scheme over `S` is
quasi-separated. -/
def forallScheme : Prop :=
  ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → QuasiSeparated pZ

/-- `forallScheme f` means every scheme-valued pullback projection of `f` is
quasi-separated. -/
theorem forallScheme_iff : forallScheme f ↔
    ∀ (Z : Over S) (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → QuasiSeparated pZ := by
  constructor
  · intro h Z P g pZ pX sq
    exact h sq
  · intro h Z P g pZ pX sq
    exact h Z P g pZ pX sq

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → QuasiSeparated pZ) : forallScheme f := by
  exact h

/-- Under `forallScheme f`, the test-leg of any scheme-valued pullback of `f` is
quasi-separated. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : QuasiSeparated pZ := by
  exact h sq

/-- The chosen pullback projection `pullback.snd f g` along a morphism from a
scheme is quasi-separated whenever `forallScheme f` holds. -/
theorem pullback_snd {Z : Over S} (h : forallScheme f) (g : ofOver Z ⟶ Y)
    [HasPullback f g] : QuasiSeparated (pullback.snd f g) := by
  exact h (IsPullback.of_hasPullback f g).flip

end forallScheme

/-- The base change of `f` along every morphism from an affine scheme over `S`
is quasi-separated. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → QuasiSeparated pZ

/-- `forallAffine f` means every affine-scheme-valued pullback projection of `f`
is quasi-separated. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → QuasiSeparated pZ := by
  constructor
  · intro h Z hZ P g pZ pX sq
    exact h sq
  · intro h Z hZ P g pZ pX sq
    exact h Z P g pZ pX sq

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses `forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → QuasiSeparated pZ) : forallAffine f := by
  exact h

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is quasi-separated. -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : QuasiSeparated pZ := by
  exact h sq

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme is quasi-separated whenever `forallAffine f` holds. -/
theorem pullback_snd {Z : Over S} [IsAffine Z.left] (h : forallAffine f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] : QuasiSeparated (pullback.snd f g) := by
  exact h (IsPullback.of_hasPullback f g).flip

end forallAffine

/-- For every affine scheme over `S` mapping to `Y`, the pullback algebraic
space is absolutely quasi-separated. -/
def forallAffineSpace : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → IsAbsolutelyQuasiSeparated P

/-- `forallAffineSpace f` means every affine-scheme-valued pullback object of
`f` is absolutely quasi-separated. -/
theorem forallAffineSpace_iff : forallAffineSpace f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → IsAbsolutelyQuasiSeparated P := by
  constructor
  · intro h Z hZ P g pZ pX sq
    exact h sq
  · intro h Z hZ P g pZ pX sq
    exact h Z P g pZ pX sq

namespace forallAffineSpace

/-- A universal affine-scheme-valued pullback-object condition witnesses
`forallAffineSpace f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → IsAbsolutelyQuasiSeparated P) :
    forallAffineSpace f := by
  exact h

/-- Under `forallAffineSpace f`, any affine-scheme-valued pullback object of `f`
is absolutely quasi-separated. -/
theorem spec (h : forallAffineSpace f) {Z : Over S} [IsAffine Z.left]
    {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : IsAbsolutelyQuasiSeparated P := by
  exact h sq

/-- The chosen pullback object `pullback f g` along a morphism from an affine
scheme is absolutely quasi-separated whenever `forallAffineSpace f` holds. -/
theorem pullback_snd {Z : Over S} [IsAffine Z.left] (h : forallAffineSpace f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] :
    IsAbsolutelyQuasiSeparated (pullback f g) := by
  exact h (IsPullback.of_hasPullback f g).flip

end forallAffineSpace

/-- There is a surjective étale morphism from a scheme to `Y` along which every
pullback of `f` is quasi-separated. -/
def existsEtaleOnTarget : Prop :=
  ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
    Etale ψ ∧ Surjective ψ ∧
      ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
        IsPullback pV pX ψ f → QuasiSeparated pV

/-- `existsEtaleOnTarget f` is the existence of a surjective étale scheme atlas
of `Y` along which pullbacks of `f` are quasi-separated. -/
theorem existsEtaleOnTarget_iff : existsEtaleOnTarget f ↔
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ (P : AlgebraicSpace S) (pV : P ⟶ ofOver V) (pX : P ⟶ X),
          IsPullback pV pX ψ f → QuasiSeparated pV := by
  constructor
  · rintro ⟨V, ψ, he, hs, h⟩
    exact ⟨V, ψ, he, hs, fun P pV pX sq => h sq⟩
  · rintro ⟨V, ψ, he, hs, h⟩
    refine ⟨V, ψ, he, hs, ?_⟩
    intro P pV pX sq
    exact h P pV pX sq

namespace existsEtaleOnTarget

/-- A surjective étale scheme atlas of `Y` with quasi-separated pullbacks of `f`
witnesses `existsEtaleOnTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
      IsPullback pV pX ψ f → QuasiSeparated pV) : existsEtaleOnTarget f := by
  exact ⟨V, ψ, inferInstance, inferInstance, h⟩

/-- `existsEtaleOnTarget f` supplies a surjective étale scheme atlas of `Y`
along which pullbacks of `f` are quasi-separated. -/
theorem spec (h : existsEtaleOnTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
          IsPullback pV pX ψ f → QuasiSeparated pV := by
  exact h

end existsEtaleOnTarget

/-- There is a Zariski covering of `Y` along which every inverse-image
projection of `f` is quasi-separated. -/
def existsZariskiCover : Prop :=
  ∃ (𝒰 : ZariskiCover.{u, u} Y),
    ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → QuasiSeparated pYi

/-- `existsZariskiCover f` is the existence of a Zariski covering of `Y` whose
inverse images under `f` map quasi-separately to the covering opens. -/
theorem existsZariskiCover_iff : existsZariskiCover f ↔
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i (P : AlgebraicSpace S) (pYi : P ⟶ 𝒰.X i) (pX : P ⟶ X),
        IsPullback pYi pX (𝒰.f i) f → QuasiSeparated pYi := by
  constructor
  · rintro ⟨𝒰, h⟩
    exact ⟨𝒰, fun i P pYi pX sq => h i sq⟩
  · rintro ⟨𝒰, h⟩
    refine ⟨𝒰, ?_⟩
    intro i P pYi pX sq
    exact h i P pYi pX sq

namespace existsZariskiCover

/-- A Zariski covering of `Y` with quasi-separated inverse-image projections of
`f` witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → QuasiSeparated pYi) :
    existsZariskiCover f := by
  exact ⟨𝒰, h⟩

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` map quasi-separately to the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → QuasiSeparated pYi := by
  exact h

end existsZariskiCover

end QuasiSeparated

namespace Separated

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`, the following are equivalent: `Separated f`; every scheme-valued
base change of `f` is separated; every affine-scheme-valued base change of `f`
is separated; for every affine scheme `Z ⟶ Y` the algebraic space `Z ×_Y X` is
absolutely separated; some surjective étale scheme atlas of `Y` has separated
pullback of `f`; and some Zariski covering of `Y` has each inverse-image
projection `f⁻¹(Yᵢ) ⟶ Yᵢ` separated. -/
theorem tfae :
    List.TFAE [Separated f, forallScheme f, forallAffine f, forallAffineSpace f,
      existsEtaleOnTarget f, existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is separated iff every scheme-valued base
change is separated. -/
theorem iff_forallScheme : Separated f ↔ forallScheme f := by
  exact (tfae f).out 0 1

/-- A morphism of algebraic spaces is separated iff every affine-scheme-valued
base change is separated. -/
theorem iff_forallAffine : Separated f ↔ forallAffine f := by
  exact (tfae f).out 0 2

/-- A morphism of algebraic spaces is separated iff every affine-scheme-valued
pullback object is absolutely separated. -/
theorem iff_forallAffineSpace : Separated f ↔ forallAffineSpace f := by
  exact (tfae f).out 0 3

/-- A morphism of algebraic spaces is separated iff some surjective étale scheme
atlas of the target has separated pullback. -/
theorem iff_existsEtaleOnTarget : Separated f ↔ existsEtaleOnTarget f := by
  exact (tfae f).out 0 4

/-- A morphism of algebraic spaces is separated iff some Zariski covering of the
target has separated inverse images under `f`. -/
theorem iff_existsZariskiCover : Separated f ↔ existsZariskiCover f := by
  exact (tfae f).out 0 5

end Separated

namespace LocallySeparated

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`, the following are equivalent: `LocallySeparated f`; every
scheme-valued base change of `f` is locally separated; every
affine-scheme-valued base change of `f` is locally separated; for every affine
scheme `Z ⟶ Y` the algebraic space `Z ×_Y X` is absolutely locally separated;
some surjective étale scheme atlas of `Y` has locally separated pullback of `f`;
and some Zariski covering of `Y` has each inverse-image projection
`f⁻¹(Yᵢ) ⟶ Yᵢ` locally separated. -/
theorem tfae :
    List.TFAE [LocallySeparated f, forallScheme f, forallAffine f, forallAffineSpace f,
      existsEtaleOnTarget f, existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is locally separated iff every scheme-valued
base change is locally separated. -/
theorem iff_forallScheme : LocallySeparated f ↔ forallScheme f := by
  exact (tfae f).out 0 1

/-- A morphism of algebraic spaces is locally separated iff every
affine-scheme-valued base change is locally separated. -/
theorem iff_forallAffine : LocallySeparated f ↔ forallAffine f := by
  exact (tfae f).out 0 2

/-- A morphism of algebraic spaces is locally separated iff every
affine-scheme-valued pullback object is absolutely locally separated. -/
theorem iff_forallAffineSpace : LocallySeparated f ↔ forallAffineSpace f := by
  exact (tfae f).out 0 3

/-- A morphism of algebraic spaces is locally separated iff some surjective
étale scheme atlas of the target has locally separated pullback. -/
theorem iff_existsEtaleOnTarget : LocallySeparated f ↔ existsEtaleOnTarget f := by
  exact (tfae f).out 0 4

/-- A morphism of algebraic spaces is locally separated iff some Zariski
covering of the target has locally separated inverse images under `f`. -/
theorem iff_existsZariskiCover : LocallySeparated f ↔ existsZariskiCover f := by
  exact (tfae f).out 0 5

end LocallySeparated

namespace QuasiSeparated

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over a
scheme `S`, the following are equivalent: `QuasiSeparated f`; every
scheme-valued base change of `f` is quasi-separated; every
affine-scheme-valued base change of `f` is quasi-separated; for every affine
scheme `Z ⟶ Y` the algebraic space `Z ×_Y X` is absolutely quasi-separated; some
surjective étale scheme atlas of `Y` has quasi-separated pullback of `f`; and
some Zariski covering of `Y` has each inverse-image projection `f⁻¹(Yᵢ) ⟶ Yᵢ`
quasi-separated. -/
theorem tfae :
    List.TFAE [QuasiSeparated f, forallScheme f, forallAffine f, forallAffineSpace f,
      existsEtaleOnTarget f, existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is quasi-separated iff every scheme-valued
base change is quasi-separated. -/
theorem iff_forallScheme : QuasiSeparated f ↔ forallScheme f := by
  exact (tfae f).out 0 1

/-- A morphism of algebraic spaces is quasi-separated iff every
affine-scheme-valued base change is quasi-separated. -/
theorem iff_forallAffine : QuasiSeparated f ↔ forallAffine f := by
  exact (tfae f).out 0 2

/-- A morphism of algebraic spaces is quasi-separated iff every
affine-scheme-valued pullback object is absolutely quasi-separated. -/
theorem iff_forallAffineSpace : QuasiSeparated f ↔ forallAffineSpace f := by
  exact (tfae f).out 0 3

/-- A morphism of algebraic spaces is quasi-separated iff some surjective étale
scheme atlas of the target has quasi-separated pullback. -/
theorem iff_existsEtaleOnTarget : QuasiSeparated f ↔ existsEtaleOnTarget f := by
  exact (tfae f).out 0 4

/-- A morphism of algebraic spaces is quasi-separated iff some Zariski covering
of the target has quasi-separated inverse images under `f`. -/
theorem iff_existsZariskiCover : QuasiSeparated f ↔ existsZariskiCover f := by
  exact (tfae f).out 0 5

end QuasiSeparated

end AlgebraicGeometry.AlgebraicSpace
