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
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.UniversallyOpen
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Locality.Criteria

/-!
# Local tests for universally open morphisms of algebraic spaces

Universal openness of a morphism of algebraic spaces is tested on scheme-valued
and affine base change, étale scheme atlases, and Zariski coverings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace UniversallyOpen

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

private theorem open_comp_iso {W V Z : AlgebraicSpace S} (e : W ≅ V)
    (g : V ⟶ Z) (h : Open g) : Open (e.hom ≫ g) := by
  let H : Points W ≃ₜ Points V :=
    { toEquiv :=
        { toFun := Points.map e.hom
          invFun := Points.map e.inv
          left_inv := by
            intro x
            rw [← Points.map_comp, e.hom_inv_id, Points.map_id]
          right_inv := by
            intro x
            rw [← Points.map_comp, e.inv_hom_id, Points.map_id] }
      continuous_toFun := Points.continuous_map e.hom
      continuous_invFun := Points.continuous_map e.inv }
  constructor
  change IsOpenMap (Points.map (e.hom ≫ g))
  have hmap : Points.map (e.hom ≫ g) = Points.map g ∘ Points.map e.hom := by
    funext x
    exact Points.map_comp _ _ x
  rw [hmap]
  exact h.isOpenMap.comp H.isOpenMap

/-- The projection of every scheme-valued base change of `f` is an open morphism
of algebraic spaces. -/
def forallScheme : Prop :=
  ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Open pZ

/-- The source-facing open test agrees with the generic chosen-pullback test
for `Open`. It does not replace openness by universal openness. -/
theorem forallScheme_iff_criteria :
    forallScheme f ↔ Locality.Criteria.forallScheme (@Open S) f := by
  constructor
  · intro h Z g
    exact h (pullbackAlongScheme.isPullback f g).flip
  · intro h Z W g pZ pX sq
    let e := sq.isoIsPullback _ _ (pullbackAlongScheme.isPullback f g).flip
    have he : e.hom ≫ pullbackAlongScheme.snd f g = pZ :=
      sq.isoIsPullback_hom_fst _ _ (pullbackAlongScheme.isPullback f g).flip
    rw [← he]
    exact open_comp_iso e _ (h g)

/-- `forallScheme f` means every scheme-valued pullback projection of `f` is
open. -/
theorem forallScheme_iff : forallScheme f ↔
    ∀ (Z : Over S) (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → Open pZ := by
  constructor
  · intro h Z P g pZ pX sq
    exact h sq
  · intro h Z P g pZ pX sq
    exact h Z P g pZ pX sq

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Open pZ) : forallScheme f := sorry

/-- Under `forallScheme f`, the test-leg of any scheme-valued pullback of `f` is
open. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Open pZ := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from a
scheme is open whenever `forallScheme f` holds. -/
theorem pullback_snd {Z : Over S} (h : forallScheme f) (g : ofOver Z ⟶ Y)
    [HasPullback f g] : Open (pullback.snd f g) := sorry

end forallScheme

/-- The projection of every affine-scheme-valued base change of `f` is an open
morphism of algebraic spaces. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Open pZ

/-- The affine open test agrees with the generic chosen-pullback test for
`Open`, with its original affine hypothesis and arbitrary-pullback interface. -/
theorem forallAffine_iff_criteria :
    forallAffine f ↔ Locality.Criteria.forallAffine (@Open S) f := by
  constructor
  · intro h Z g hZ
    letI := hZ
    exact h (pullbackAlongScheme.isPullback f g).flip
  · intro h Z hZ W g pZ pX sq
    let e := sq.isoIsPullback _ _ (pullbackAlongScheme.isPullback f g).flip
    have he : e.hom ≫ pullbackAlongScheme.snd f g = pZ :=
      sq.isoIsPullback_hom_fst _ _ (pullbackAlongScheme.isPullback f g).flip
    rw [← he]
    exact open_comp_iso e _ (h g hZ)

/-- `forallAffine f` means every affine-scheme-valued pullback projection of `f`
is open. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → Open pZ := sorry

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses `forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Open pZ) : forallAffine f := sorry

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is open. -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Open pZ := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme is open whenever `forallAffine f` holds. -/
theorem pullback_snd {Z : Over S} [IsAffine Z.left] (h : forallAffine f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] : Open (pullback.snd f g) := sorry

end forallAffine

/-- There is a surjective étale morphism from a scheme to `Y` along which every
pullback of `f` is universally open. -/
abbrev existsEtaleOnTarget : Prop :=
  Locality.Criteria.existsEtaleOnTarget (@UniversallyOpen S) f

/-- `existsEtaleOnTarget f` is the existence of a surjective étale scheme atlas
of `Y` along which pullbacks of `f` are universally open. -/
theorem existsEtaleOnTarget_iff : existsEtaleOnTarget f ↔
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ (P : AlgebraicSpace S) (pV : P ⟶ ofOver V) (pX : P ⟶ X),
          IsPullback pV pX ψ f → UniversallyOpen pV := sorry

namespace existsEtaleOnTarget

/-- A surjective étale scheme atlas of `Y` with universally open pullbacks of
`f` witnesses `existsEtaleOnTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
      IsPullback pV pX ψ f → UniversallyOpen pV) : existsEtaleOnTarget f := sorry

/-- `existsEtaleOnTarget f` supplies a surjective étale scheme atlas of `Y`
along which pullbacks of `f` are universally open. -/
theorem spec (h : existsEtaleOnTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
          IsPullback pV pX ψ f → UniversallyOpen pV := sorry

end existsEtaleOnTarget

/-- There is a Zariski covering of `Y` along which every inverse-image
projection of `f` is universally open. -/
def existsZariskiCover : Prop :=
  ∃ (𝒰 : ZariskiCover.{u, u} Y),
    ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → UniversallyOpen pYi

/-- `existsZariskiCover f` is the existence of a Zariski covering of `Y` whose
inverse images under `f` map universally openly to the covering opens. -/
theorem existsZariskiCover_iff : existsZariskiCover f ↔
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i (P : AlgebraicSpace S) (pYi : P ⟶ 𝒰.X i) (pX : P ⟶ X),
        IsPullback pYi pX (𝒰.f i) f → UniversallyOpen pYi := sorry

namespace existsZariskiCover

/-- A Zariski covering of `Y` with universally open inverse-image projections of
`f` witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → UniversallyOpen pYi) :
    existsZariskiCover f := sorry

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` map universally openly to the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → UniversallyOpen pYi := sorry

end existsZariskiCover

/-- The chosen pullback projection `pullback.snd f g` along a morphism from a
scheme is open whenever `f` is universally open. -/
theorem pullback_snd_ofOver {Z : Over S} [UniversallyOpen f] (g : ofOver Z ⟶ Y)
    [HasPullback f g] : Open (pullback.snd f g) := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme is open whenever `f` is universally open. -/
theorem pullback_snd_ofOver_affine {Z : Over S} [IsAffine Z.left]
    [UniversallyOpen f] (g : ofOver Z ⟶ Y) [HasPullback f g] :
    Open (pullback.snd f g) := sorry

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the following are equivalent: `UniversallyOpen f`; every scheme-valued
base change of `f` has open projection `|Z ×_Y X| ⟶ |Z|`; every
affine-scheme-valued base change of `f` has open projection `|Z ×_Y X| ⟶ |Z|`;
some surjective étale scheme atlas of `Y` has universally open pullback of `f`;
and some Zariski covering of `Y` has each inverse-image projection
`f⁻¹(Yᵢ) ⟶ Yᵢ` universally open. -/
theorem tfae :
    List.TFAE [UniversallyOpen f, forallScheme f, forallAffine f, existsEtaleOnTarget f,
      existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is universally open iff every scheme-valued
base change has open projection. -/
theorem iff_forallScheme : UniversallyOpen f ↔ forallScheme f := sorry

/-- A morphism of algebraic spaces is universally open iff every
affine-scheme-valued base change has open projection. -/
theorem iff_forallAffine : UniversallyOpen f ↔ forallAffine f := sorry

/-- A morphism of algebraic spaces is universally open iff some surjective étale
scheme atlas of the target has universally open pullback. -/
theorem iff_existsEtaleOnTarget : UniversallyOpen f ↔ existsEtaleOnTarget f := sorry

/-- A morphism of algebraic spaces is universally open iff some Zariski covering
of the target has universally open inverse images under `f`. -/
theorem iff_existsZariskiCover : UniversallyOpen f ↔ existsZariskiCover f := sorry

end UniversallyOpen

end AlgebraicGeometry.AlgebraicSpace
