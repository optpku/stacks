module

public import Mathlib.Data.List.TFAE
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Proper
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

/-!
# Local characterizations of proper morphisms of algebraic spaces

Properness is equivalent to properness after every scheme-valued or affine
base change, after base change along some surjective étale scheme atlas of
the target, and over some Zariski covering of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Proper

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- The projection of every scheme-valued base change of `f` is proper. -/
def forallScheme : Prop :=
  ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Proper pZ

/-- `forallScheme f` means every scheme-valued pullback projection of `f` is
proper. -/
theorem forallScheme_iff : forallScheme f ↔
    ∀ (Z : Over S) (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → Proper pZ := sorry

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Proper pZ) : forallScheme f := sorry

/-- Under `forallScheme f`, the test-leg of any scheme-valued pullback of `f` is
proper. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Proper pZ := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from a
scheme is proper whenever `forallScheme f` holds. -/
theorem pullback_snd {Z : Over S} (h : forallScheme f) (g : ofOver Z ⟶ Y)
    [HasPullback f g] : Proper (pullback.snd f g) := sorry

end forallScheme

/-- The projection of every affine-scheme-valued base change of `f` is proper. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Proper pZ

/-- `forallAffine f` means every affine-scheme-valued pullback projection of `f`
is proper. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → Proper pZ := sorry

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses
`forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Proper pZ) : forallAffine f := sorry

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is proper. -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Proper pZ := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme is proper whenever `forallAffine f` holds. -/
theorem pullback_snd {Z : Over S} [IsAffine Z.left] (h : forallAffine f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] : Proper (pullback.snd f g) := sorry

end forallAffine

/-- There is a surjective étale morphism from a scheme to `Y` along which every
pullback of `f` is proper. -/
def existsEtaleOnTarget : Prop :=
  ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
    Etale ψ ∧ Surjective ψ ∧
      ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
        IsPullback pV pX ψ f → Proper pV

/-- `existsEtaleOnTarget f` is the existence of a surjective étale scheme atlas
of `Y` along which pullbacks of `f` are proper. -/
theorem existsEtaleOnTarget_iff : existsEtaleOnTarget f ↔
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ (P : AlgebraicSpace S) (pV : P ⟶ ofOver V) (pX : P ⟶ X),
          IsPullback pV pX ψ f → Proper pV := sorry

namespace existsEtaleOnTarget

/-- A surjective étale scheme atlas of `Y` with proper pullbacks of `f`
witnesses `existsEtaleOnTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
      IsPullback pV pX ψ f → Proper pV) :
    existsEtaleOnTarget f := sorry

/-- `existsEtaleOnTarget f` supplies a surjective étale scheme atlas of `Y`
along which pullbacks of `f` are proper. -/
theorem spec (h : existsEtaleOnTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
          IsPullback pV pX ψ f → Proper pV := sorry

end existsEtaleOnTarget

/-- There is a Zariski covering of `Y` along which every inverse-image
projection of `f` is proper. -/
def existsZariskiCover : Prop :=
  ∃ (𝒰 : ZariskiCover.{u, u} Y),
    ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → Proper pYi

/-- `existsZariskiCover f` is the existence of a Zariski covering of `Y` whose
inverse images under `f` are proper over the covering opens. -/
theorem existsZariskiCover_iff : existsZariskiCover f ↔
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i (P : AlgebraicSpace S) (pYi : P ⟶ 𝒰.X i) (pX : P ⟶ X),
        IsPullback pYi pX (𝒰.f i) f → Proper pYi := sorry

namespace existsZariskiCover

/-- A Zariski covering of `Y` with proper inverse-image projections of `f`
witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → Proper pYi) :
    existsZariskiCover f := sorry

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` are proper over the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → Proper pYi := sorry

end existsZariskiCover

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the following are equivalent: `Proper f`; every scheme-valued base change
of `f` has proper projection; every affine-scheme-valued base change of `f` has
proper projection; some surjective étale scheme atlas of `Y` has proper
pullback of `f`; and some Zariski covering of `Y` has each inverse-image
projection `f⁻¹(Yᵢ) ⟶ Yᵢ` proper. -/
@[stacks 083R]
theorem tfae :
    List.TFAE [Proper f, forallScheme f, forallAffine f, existsEtaleOnTarget f,
      existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is proper iff every scheme-valued base
change has proper projection. -/
theorem iff_forallScheme : Proper f ↔ forallScheme f := sorry

/-- A morphism of algebraic spaces is proper iff every affine-scheme-valued
base change has proper projection. -/
theorem iff_forallAffine : Proper f ↔ forallAffine f := sorry

/-- A morphism of algebraic spaces is proper iff some surjective étale scheme
atlas of the target has proper pullback. -/
theorem iff_existsEtaleOnTarget : Proper f ↔ existsEtaleOnTarget f := sorry

/-- A morphism of algebraic spaces is proper iff some Zariski covering of the
target has proper inverse images under `f`. -/
theorem iff_existsZariskiCover : Proper f ↔ existsZariskiCover f := sorry

end Proper

end AlgebraicGeometry.AlgebraicSpace
