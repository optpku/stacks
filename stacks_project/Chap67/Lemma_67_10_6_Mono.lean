/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap65.Definition_65_12_5_ZariskiCover
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective

/-!
# Characterizations of monomorphisms of algebraic spaces

Monomorphisms of algebraic spaces are tested on scheme-valued base change, étale
scheme atlases, and Zariski coverings.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Monomorphisms

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- The base change of `f` along every morphism from a scheme over `S` is a
monomorphism. -/
def forallScheme : Prop :=
  ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Mono pZ

/-- `forallScheme f` means every scheme-valued pullback projection of `f` is a
monomorphism. -/
theorem forallScheme_iff : forallScheme f ↔
    ∀ (Z : Over S) (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → Mono pZ := sorry

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Mono pZ) : forallScheme f := sorry

/-- Under `forallScheme f`, the test-leg of any scheme-valued pullback of `f` is
a monomorphism. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Mono pZ := sorry

end forallScheme

/-- The base change of `f` along every morphism from an affine scheme over `S`
is a monomorphism. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Mono pZ

/-- `forallAffine f` means every affine-scheme-valued pullback projection of `f`
is a monomorphism. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → Mono pZ := sorry

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses `forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Mono pZ) : forallAffine f := sorry

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is a monomorphism. -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Mono pZ := sorry

end forallAffine

/-- There is a surjective étale morphism from a scheme to `Y` along which every
pullback of `f` is a monomorphism. -/
def existsEtaleOnTarget : Prop :=
  ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
    Etale ψ ∧ Surjective ψ ∧
      ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
        IsPullback pV pX ψ f → Mono pV

/-- `existsEtaleOnTarget f` is the existence of a surjective étale scheme atlas
of `Y` along which pullbacks of `f` are monomorphisms. -/
theorem existsEtaleOnTarget_iff : existsEtaleOnTarget f ↔
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ (P : AlgebraicSpace S) (pV : P ⟶ ofOver V) (pX : P ⟶ X),
          IsPullback pV pX ψ f → Mono pV := sorry

namespace existsEtaleOnTarget

/-- A surjective étale scheme atlas of `Y` with monomorphic pullbacks of `f`
witnesses `existsEtaleOnTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
      IsPullback pV pX ψ f → Mono pV) : existsEtaleOnTarget f := sorry

/-- `existsEtaleOnTarget f` supplies a surjective étale scheme atlas of `Y`
along which pullbacks of `f` are monomorphisms. -/
theorem spec (h : existsEtaleOnTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
          IsPullback pV pX ψ f → Mono pV := sorry

end existsEtaleOnTarget

/-- There is a Zariski covering of `Y` along which every inverse-image
projection of `f` is a monomorphism. -/
def existsZariskiCover : Prop :=
  ∃ (𝒰 : ZariskiCover.{u, u} Y),
    ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → Mono pYi

/-- `existsZariskiCover f` is the existence of a Zariski covering of `Y` whose
inverse images under `f` map monomorphically to the covering opens. -/
theorem existsZariskiCover_iff : existsZariskiCover f ↔
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i (P : AlgebraicSpace S) (pYi : P ⟶ 𝒰.X i) (pX : P ⟶ X),
        IsPullback pYi pX (𝒰.f i) f → Mono pYi := sorry

namespace existsZariskiCover

/-- A Zariski covering of `Y` with monomorphic inverse-image projections of `f`
witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → Mono pYi) :
    existsZariskiCover f := sorry

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` map monomorphically to the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → Mono pYi := sorry

end existsZariskiCover

/-- The chosen pullback projection `pullback.snd f g` along a morphism from a
scheme is a monomorphism whenever `f` is a monomorphism. -/
theorem pullback_snd_ofOver {Z : Over S} [Mono f] (g : ofOver Z ⟶ Y)
    [HasPullback f g] : Mono (pullback.snd f g) := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme is a monomorphism whenever `f` is a monomorphism. -/
theorem pullback_snd_ofOver_affine {Z : Over S} [IsAffine Z.left] [Mono f]
    (g : ofOver Z ⟶ Y) [HasPullback f g] : Mono (pullback.snd f g) := sorry

end Monomorphisms

end AlgebraicGeometry.AlgebraicSpace
