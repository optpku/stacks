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
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Definition_66_3_1_Separation
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_4_2_Separation
public import stacks_project.Chap67.Definition_67_5_2_Surjective

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
      IsPullback pZ pX g f → Separated pZ := sorry

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Separated pZ) : forallScheme f := sorry

/-- Under `forallScheme f`, the test-leg of any scheme-valued pullback of `f` is
separated. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Separated pZ := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from a
scheme is separated whenever `forallScheme f` holds. -/
theorem pullback_snd {Z : Over S} (h : forallScheme f) (g : ofOver Z ⟶ Y)
    [HasPullback f g] : Separated (pullback.snd f g) := sorry

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
      IsPullback pZ pX g f → Separated pZ := sorry

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses `forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Separated pZ) : forallAffine f := sorry

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is separated. -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Separated pZ := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme is separated whenever `forallAffine f` holds. -/
theorem pullback_snd {Z : Over S} [IsAffine Z.left] (h : forallAffine f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] : Separated (pullback.snd f g) := sorry

end forallAffine

/-- For every affine scheme over `S` mapping to `Y`, the pullback algebraic
space is absolutely separated in the sense of Definition 66.3.1. -/
def forallAffineSpace : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → IsAbsolutelySeparated P

/-- `forallAffineSpace f` means every affine-scheme-valued pullback object of
`f` is absolutely separated. -/
theorem forallAffineSpace_iff : forallAffineSpace f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → IsAbsolutelySeparated P := sorry

namespace forallAffineSpace

/-- A universal affine-scheme-valued pullback-object condition witnesses
`forallAffineSpace f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → IsAbsolutelySeparated P) : forallAffineSpace f := sorry

/-- Under `forallAffineSpace f`, any affine-scheme-valued pullback object of `f`
is absolutely separated. -/
theorem spec (h : forallAffineSpace f) {Z : Over S} [IsAffine Z.left]
    {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : IsAbsolutelySeparated P := sorry

/-- The chosen pullback object `pullback f g` along a morphism from an affine
scheme is absolutely separated whenever `forallAffineSpace f` holds. -/
theorem pullback_snd {Z : Over S} [IsAffine Z.left] (h : forallAffineSpace f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] : IsAbsolutelySeparated (pullback f g) := sorry

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
          IsPullback pV pX ψ f → Separated pV := sorry

namespace existsEtaleOnTarget

/-- A surjective étale scheme atlas of `Y` with separated pullbacks of `f`
witnesses `existsEtaleOnTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
      IsPullback pV pX ψ f → Separated pV) : existsEtaleOnTarget f := sorry

/-- `existsEtaleOnTarget f` supplies a surjective étale scheme atlas of `Y`
along which pullbacks of `f` are separated. -/
theorem spec (h : existsEtaleOnTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
          IsPullback pV pX ψ f → Separated pV := sorry

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
        IsPullback pYi pX (𝒰.f i) f → Separated pYi := sorry

namespace existsZariskiCover

/-- A Zariski covering of `Y` with separated inverse-image projections of `f`
witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → Separated pYi) :
    existsZariskiCover f := sorry

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` map separately to the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → Separated pYi := sorry

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
      IsPullback pZ pX g f → LocallySeparated pZ := sorry

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → LocallySeparated pZ) : forallScheme f := sorry

/-- Under `forallScheme f`, the test-leg of any scheme-valued pullback of `f` is
locally separated. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : LocallySeparated pZ := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from a
scheme is locally separated whenever `forallScheme f` holds. -/
theorem pullback_snd {Z : Over S} (h : forallScheme f) (g : ofOver Z ⟶ Y)
    [HasPullback f g] : LocallySeparated (pullback.snd f g) := sorry

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
      IsPullback pZ pX g f → LocallySeparated pZ := sorry

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses `forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → LocallySeparated pZ) : forallAffine f := sorry

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is locally separated. -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : LocallySeparated pZ := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme is locally separated whenever `forallAffine f` holds. -/
theorem pullback_snd {Z : Over S} [IsAffine Z.left] (h : forallAffine f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] : LocallySeparated (pullback.snd f g) := sorry

end forallAffine

/-- For every affine scheme over `S` mapping to `Y`, the pullback algebraic
space is absolutely locally separated in the sense of Definition 66.3.1. -/
def forallAffineSpace : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → IsAbsolutelyLocallySeparated P

/-- `forallAffineSpace f` means every affine-scheme-valued pullback object of
`f` is absolutely locally separated. -/
theorem forallAffineSpace_iff : forallAffineSpace f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → IsAbsolutelyLocallySeparated P := sorry

namespace forallAffineSpace

/-- A universal affine-scheme-valued pullback-object condition witnesses
`forallAffineSpace f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → IsAbsolutelyLocallySeparated P) :
    forallAffineSpace f := sorry

/-- Under `forallAffineSpace f`, any affine-scheme-valued pullback object of `f`
is absolutely locally separated. -/
theorem spec (h : forallAffineSpace f) {Z : Over S} [IsAffine Z.left]
    {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : IsAbsolutelyLocallySeparated P := sorry

/-- The chosen pullback object `pullback f g` along a morphism from an affine
scheme is absolutely locally separated whenever `forallAffineSpace f` holds. -/
theorem pullback_snd {Z : Over S} [IsAffine Z.left] (h : forallAffineSpace f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] :
    IsAbsolutelyLocallySeparated (pullback f g) := sorry

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
          IsPullback pV pX ψ f → LocallySeparated pV := sorry

namespace existsEtaleOnTarget

/-- A surjective étale scheme atlas of `Y` with locally separated pullbacks of
`f` witnesses `existsEtaleOnTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
      IsPullback pV pX ψ f → LocallySeparated pV) : existsEtaleOnTarget f := sorry

/-- `existsEtaleOnTarget f` supplies a surjective étale scheme atlas of `Y`
along which pullbacks of `f` are locally separated. -/
theorem spec (h : existsEtaleOnTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
          IsPullback pV pX ψ f → LocallySeparated pV := sorry

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
        IsPullback pYi pX (𝒰.f i) f → LocallySeparated pYi := sorry

namespace existsZariskiCover

/-- A Zariski covering of `Y` with locally separated inverse-image projections
of `f` witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → LocallySeparated pYi) :
    existsZariskiCover f := sorry

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` map locally separately to the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → LocallySeparated pYi := sorry

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
      IsPullback pZ pX g f → QuasiSeparated pZ := sorry

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → QuasiSeparated pZ) : forallScheme f := sorry

/-- Under `forallScheme f`, the test-leg of any scheme-valued pullback of `f` is
quasi-separated. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : QuasiSeparated pZ := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from a
scheme is quasi-separated whenever `forallScheme f` holds. -/
theorem pullback_snd {Z : Over S} (h : forallScheme f) (g : ofOver Z ⟶ Y)
    [HasPullback f g] : QuasiSeparated (pullback.snd f g) := sorry

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
      IsPullback pZ pX g f → QuasiSeparated pZ := sorry

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses `forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → QuasiSeparated pZ) : forallAffine f := sorry

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is quasi-separated. -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : QuasiSeparated pZ := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme is quasi-separated whenever `forallAffine f` holds. -/
theorem pullback_snd {Z : Over S} [IsAffine Z.left] (h : forallAffine f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] : QuasiSeparated (pullback.snd f g) := sorry

end forallAffine

/-- For every affine scheme over `S` mapping to `Y`, the pullback algebraic
space is absolutely quasi-separated in the sense of Definition 66.3.1. -/
def forallAffineSpace : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → IsAbsolutelyQuasiSeparated P

/-- `forallAffineSpace f` means every affine-scheme-valued pullback object of
`f` is absolutely quasi-separated. -/
theorem forallAffineSpace_iff : forallAffineSpace f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (P : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : P ⟶ ofOver Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → IsAbsolutelyQuasiSeparated P := sorry

namespace forallAffineSpace

/-- A universal affine-scheme-valued pullback-object condition witnesses
`forallAffineSpace f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {P : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → IsAbsolutelyQuasiSeparated P) :
    forallAffineSpace f := sorry

/-- Under `forallAffineSpace f`, any affine-scheme-valued pullback object of `f`
is absolutely quasi-separated. -/
theorem spec (h : forallAffineSpace f) {Z : Over S} [IsAffine Z.left]
    {P : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : P ⟶ ofOver Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : IsAbsolutelyQuasiSeparated P := sorry

/-- The chosen pullback object `pullback f g` along a morphism from an affine
scheme is absolutely quasi-separated whenever `forallAffineSpace f` holds. -/
theorem pullback_snd {Z : Over S} [IsAffine Z.left] (h : forallAffineSpace f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] :
    IsAbsolutelyQuasiSeparated (pullback f g) := sorry

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
          IsPullback pV pX ψ f → QuasiSeparated pV := sorry

namespace existsEtaleOnTarget

/-- A surjective étale scheme atlas of `Y` with quasi-separated pullbacks of `f`
witnesses `existsEtaleOnTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
      IsPullback pV pX ψ f → QuasiSeparated pV) : existsEtaleOnTarget f := sorry

/-- `existsEtaleOnTarget f` supplies a surjective étale scheme atlas of `Y`
along which pullbacks of `f` are quasi-separated. -/
theorem spec (h : existsEtaleOnTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ {P : AlgebraicSpace S} {pV : P ⟶ ofOver V} {pX : P ⟶ X},
          IsPullback pV pX ψ f → QuasiSeparated pV := sorry

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
        IsPullback pYi pX (𝒰.f i) f → QuasiSeparated pYi := sorry

namespace existsZariskiCover

/-- A Zariski covering of `Y` with quasi-separated inverse-image projections of
`f` witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → QuasiSeparated pYi) :
    existsZariskiCover f := sorry

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` map quasi-separately to the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {P : AlgebraicSpace S} {pYi : P ⟶ 𝒰.X i} {pX : P ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → QuasiSeparated pYi := sorry

end existsZariskiCover

end QuasiSeparated

end AlgebraicGeometry.AlgebraicSpace
