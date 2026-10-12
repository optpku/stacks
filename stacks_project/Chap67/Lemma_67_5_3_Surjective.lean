/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap65.Definition_65_12_5_ZariskiCover
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective

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
      IsPullback pZ pX g f → Surjective pZ := sorry

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Surjective pZ) : forallScheme f := sorry

/-- Under `forallScheme f`, the test-leg of any scheme-valued pullback of `f` is
surjective. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Surjective pZ := sorry

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
      IsPullback pZ pX g f → Surjective pZ := sorry

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses `forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Surjective pZ) : forallAffine f := sorry

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is surjective. -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Surjective pZ := sorry

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
          IsPullback pV pX ψ f → Surjective pV := sorry

namespace existsEtaleOnTarget

/-- A surjective étale scheme atlas of `Y` with surjective pullbacks of `f`
witnesses `existsEtaleOnTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
      IsPullback pV pX ψ f → Surjective pV) : existsEtaleOnTarget f := sorry

/-- `existsEtaleOnTarget f` supplies a surjective étale scheme atlas of `Y`
along which pullbacks of `f` are surjective. -/
theorem spec (h : existsEtaleOnTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
          IsPullback pV pX ψ f → Surjective pV := sorry

end existsEtaleOnTarget

/-- There is a surjective étale morphism from a scheme to `X` whose composite
with `f` is surjective. -/
def existsEtaleOnSource : Prop :=
  ∃ (U : Over S) (φ : ofOver U ⟶ X), Etale φ ∧ Surjective φ ∧ Surjective (φ ≫ f)

/-- `existsEtaleOnSource f` is the existence of a surjective étale scheme atlas
of `X` whose composite with `f` is surjective. -/
theorem existsEtaleOnSource_iff : existsEtaleOnSource f ↔
    ∃ (U : Over S) (φ : ofOver U ⟶ X),
      Etale φ ∧ Surjective φ ∧ Surjective (φ ≫ f) := sorry

namespace existsEtaleOnSource

/-- A surjective étale scheme atlas of `X` with surjective composite with `f`
witnesses `existsEtaleOnSource f`. -/
theorem of {U : Over S} (φ : ofOver U ⟶ X) [Etale φ] [Surjective φ]
    (h : Surjective (φ ≫ f)) : existsEtaleOnSource f := sorry

/-- `existsEtaleOnSource f` supplies a surjective étale scheme atlas of `X`
whose composite with `f` is surjective. -/
theorem spec (h : existsEtaleOnSource f) :
    ∃ (U : Over S) (φ : ofOver U ⟶ X),
      Etale φ ∧ Surjective φ ∧ Surjective (φ ≫ f) := sorry

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
        Surjective h := sorry

namespace existsEtaleSquare

/-- A commutative square of surjective étale scheme atlases with surjective top
arrow witnesses `existsEtaleSquare f`. -/
theorem of {U V : Over S} {φ : ofOver U ⟶ X} {ψ : ofOver V ⟶ Y}
    {h : ofOver U ⟶ ofOver V} (sq : CommSq h φ ψ f)
    [Etale φ] [Surjective φ] [Etale ψ] [Surjective ψ] [Surjective h] :
    existsEtaleSquare f := sorry

/-- `existsEtaleSquare f` supplies a commutative square of surjective étale
scheme atlases over `f` with surjective top arrow. -/
theorem spec (h : existsEtaleSquare f) :
    ∃ (U V : Over S) (φ : ofOver U ⟶ X) (ψ : ofOver V ⟶ Y)
      (h : ofOver U ⟶ ofOver V),
      CommSq h φ ψ f ∧ Etale φ ∧ Surjective φ ∧ Etale ψ ∧ Surjective ψ ∧
        Surjective h := sorry

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
        IsPullback pYi pX (𝒰.f i) f → Surjective pYi := sorry

namespace existsZariskiCover

/-- A Zariski covering of `Y` with surjective inverse-image projections of `f`
witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → Surjective pYi) :
    existsZariskiCover f := sorry

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` map surjectively to the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → Surjective pYi := sorry

end existsZariskiCover

/-- The chosen pullback projection `pullback.snd f g` along a morphism from a
scheme is surjective whenever `f` is surjective. -/
theorem pullback_snd_ofOver {Z : Over S} [Surjective f] (g : ofOver Z ⟶ Y)
    [HasPullback f g] : Surjective (pullback.snd f g) := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme is surjective whenever `f` is surjective. -/
theorem pullback_snd_ofOver_affine {Z : Over S} [IsAffine Z.left] [Surjective f]
    (g : ofOver Z ⟶ Y) [HasPullback f g] : Surjective (pullback.snd f g) := sorry

end Surjective

end AlgebraicGeometry.AlgebraicSpace
