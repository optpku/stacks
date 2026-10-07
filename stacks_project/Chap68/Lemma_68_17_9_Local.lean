module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap65.Definition_65_12_5_ZariskiCover
public import stacks_project.Chap65.Lemma_65_6_2_OfOver
public import stacks_project.Chap66.Lemma_66_16_4_Etale
public import stacks_project.Chap67.Definition_67_5_2_Surjective
public import stacks_project.Chap68.Lemma_68_17_4_Relative
public import stacks_project.Chap68.Remark_68_17_10_VeryReasonable

/-!
# Local tests for relative property (β), decent, reasonable, and very reasonable morphisms

These morphism classes of algebraic spaces may be tested on affine-scheme-valued
base change, on the resulting pullback spaces, on a Zariski covering of the
target, and — except for very reasonable morphisms — on a surjective étale
scheme atlas of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace PropertyBeta

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- The projection of every affine-scheme-valued base change of `f` has
property (β). -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {W : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
    IsPullback pZ pX g f → PropertyBeta pZ

/-- `forallAffine f` means every affine-scheme-valued pullback projection of `f`
has property (β). -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (W : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : W ⟶ ofOver Z) (pX : W ⟶ X),
      IsPullback pZ pX g f → PropertyBeta pZ := sorry

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses
`forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {W : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
    IsPullback pZ pX g f → PropertyBeta pZ) : forallAffine f := sorry

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` has property (β). -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {W : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z}
    {pX : W ⟶ X} (sq : IsPullback pZ pX g f) : PropertyBeta pZ := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme has property (β) whenever `forallAffine f` holds. -/
theorem pullback_snd {Z : Over S} [IsAffine Z.left] (h : forallAffine f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] : PropertyBeta (pullback.snd f g) := sorry

end forallAffine

/-- Every affine-scheme-valued pullback of the source of `f` has property (β) as an
algebraic space. -/
def forallAffineObject : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {W : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
    IsPullback pZ pX g f → HasPropertyBeta W

/-- `forallAffineObject f` means every affine-scheme-valued pullback of the
source of `f` has property (β). -/
theorem forallAffineObject_iff : forallAffineObject f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (W : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : W ⟶ ofOver Z) (pX : W ⟶ X),
      IsPullback pZ pX g f → HasPropertyBeta W := sorry

namespace forallAffineObject

/-- A universal affine-scheme-valued pullback condition on the source witnesses
`forallAffineObject f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {W : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
    IsPullback pZ pX g f → HasPropertyBeta W) : forallAffineObject f := sorry

/-- Under `forallAffineObject f`, the vertex of any affine-scheme-valued
pullback of `f` has property (β). -/
theorem spec (h : forallAffineObject f) {Z : Over S} [IsAffine Z.left]
    {W : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z}
    {pX : W ⟶ X} (sq : IsPullback pZ pX g f) : HasPropertyBeta W := sorry

/-- The chosen pullback `pullback f g` along a morphism from an affine scheme is
property (β) whenever `forallAffineObject f` holds. -/
theorem pullback {Z : Over S} [IsAffine Z.left] (h : forallAffineObject f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] : HasPropertyBeta (Limits.pullback f g) := sorry

end forallAffineObject

/-- There is a Zariski covering of `Y` along which every inverse-image
projection of `f` has property (β). -/
def existsZariskiCover : Prop :=
  ∃ (𝒰 : ZariskiCover.{u, u} Y),
    ∀ i {W : AlgebraicSpace S} {pYi : W ⟶ 𝒰.X i} {pX : W ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → PropertyBeta pYi

/-- `existsZariskiCover f` is the existence of a Zariski covering of `Y` whose
inverse images under `f` have property (β) over the covering opens. -/
theorem existsZariskiCover_iff : existsZariskiCover f ↔
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i (W : AlgebraicSpace S) (pYi : W ⟶ 𝒰.X i) (pX : W ⟶ X),
        IsPullback pYi pX (𝒰.f i) f → PropertyBeta pYi := sorry

namespace existsZariskiCover

/-- A Zariski covering of `Y` with inverse-image projections of `f` having
property (β) witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {W : AlgebraicSpace S} {pYi : W ⟶ 𝒰.X i} {pX : W ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → PropertyBeta pYi) :
    existsZariskiCover f := sorry

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` have property (β) over the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {W : AlgebraicSpace S} {pYi : W ⟶ 𝒰.X i} {pX : W ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → PropertyBeta pYi := sorry

end existsZariskiCover

/-- There is a surjective étale morphism from a scheme to `Y` along which every
pullback of `f` has property (β). -/
def existsEtaleOnTarget : Prop :=
  ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
    Etale ψ ∧ Surjective ψ ∧
      ∀ {W : AlgebraicSpace S} {pV : W ⟶ ofOver V} {pX : W ⟶ X},
        IsPullback pV pX ψ f → PropertyBeta pV

/-- `existsEtaleOnTarget f` is the existence of a surjective étale scheme atlas
of `Y` along which pullbacks of `f` have property (β). -/
theorem existsEtaleOnTarget_iff : existsEtaleOnTarget f ↔
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ (W : AlgebraicSpace S) (pV : W ⟶ ofOver V) (pX : W ⟶ X),
          IsPullback pV pX ψ f → PropertyBeta pV := sorry

namespace existsEtaleOnTarget

/-- A surjective étale scheme atlas of `Y` with pullbacks of `f` having property (β)
witnesses `existsEtaleOnTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ {W : AlgebraicSpace S} {pV : W ⟶ ofOver V} {pX : W ⟶ X},
      IsPullback pV pX ψ f → PropertyBeta pV) :
    existsEtaleOnTarget f := sorry

/-- `existsEtaleOnTarget f` supplies a surjective étale scheme atlas of `Y`
along which pullbacks of `f` have property (β). -/
theorem spec (h : existsEtaleOnTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ {W : AlgebraicSpace S} {pV : W ⟶ ofOver V} {pX : W ⟶ X},
          IsPullback pV pX ψ f → PropertyBeta pV := sorry

end existsEtaleOnTarget

end PropertyBeta

namespace Decent

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- The projection of every affine-scheme-valued base change of `f` is
decent. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {W : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
    IsPullback pZ pX g f → Decent pZ

/-- `forallAffine f` means every affine-scheme-valued pullback projection of `f`
is decent. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (W : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : W ⟶ ofOver Z) (pX : W ⟶ X),
      IsPullback pZ pX g f → Decent pZ := sorry

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses
`forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {W : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
    IsPullback pZ pX g f → Decent pZ) : forallAffine f := sorry

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is decent. -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {W : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z}
    {pX : W ⟶ X} (sq : IsPullback pZ pX g f) : Decent pZ := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme is decent whenever `forallAffine f` holds. -/
theorem pullback_snd {Z : Over S} [IsAffine Z.left] (h : forallAffine f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] : Decent (pullback.snd f g) := sorry

end forallAffine

/-- Every affine-scheme-valued pullback of the source of `f` is decent as an
algebraic space. -/
def forallAffineObject : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {W : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
    IsPullback pZ pX g f → IsDecent W

/-- `forallAffineObject f` means every affine-scheme-valued pullback of the
source of `f` is decent. -/
theorem forallAffineObject_iff : forallAffineObject f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (W : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : W ⟶ ofOver Z) (pX : W ⟶ X),
      IsPullback pZ pX g f → IsDecent W := sorry

namespace forallAffineObject

/-- A universal affine-scheme-valued pullback condition on the source witnesses
`forallAffineObject f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {W : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
    IsPullback pZ pX g f → IsDecent W) : forallAffineObject f := sorry

/-- Under `forallAffineObject f`, the vertex of any affine-scheme-valued
pullback of `f` is decent. -/
theorem spec (h : forallAffineObject f) {Z : Over S} [IsAffine Z.left]
    {W : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z}
    {pX : W ⟶ X} (sq : IsPullback pZ pX g f) : IsDecent W := sorry

/-- The chosen pullback `pullback f g` along a morphism from an affine scheme is
decent whenever `forallAffineObject f` holds. -/
theorem pullback {Z : Over S} [IsAffine Z.left] (h : forallAffineObject f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] : IsDecent (Limits.pullback f g) := sorry

end forallAffineObject

/-- There is a Zariski covering of `Y` along which every inverse-image
projection of `f` is decent. -/
def existsZariskiCover : Prop :=
  ∃ (𝒰 : ZariskiCover.{u, u} Y),
    ∀ i {W : AlgebraicSpace S} {pYi : W ⟶ 𝒰.X i} {pX : W ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → Decent pYi

/-- `existsZariskiCover f` is the existence of a Zariski covering of `Y` whose
inverse images under `f` are decent over the covering opens. -/
theorem existsZariskiCover_iff : existsZariskiCover f ↔
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i (W : AlgebraicSpace S) (pYi : W ⟶ 𝒰.X i) (pX : W ⟶ X),
        IsPullback pYi pX (𝒰.f i) f → Decent pYi := sorry

namespace existsZariskiCover

/-- A Zariski covering of `Y` with decent inverse-image projections of `f`
witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {W : AlgebraicSpace S} {pYi : W ⟶ 𝒰.X i} {pX : W ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → Decent pYi) :
    existsZariskiCover f := sorry

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` are decent over the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {W : AlgebraicSpace S} {pYi : W ⟶ 𝒰.X i} {pX : W ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → Decent pYi := sorry

end existsZariskiCover

/-- There is a surjective étale morphism from a scheme to `Y` along which every
pullback of `f` is decent. -/
def existsEtaleOnTarget : Prop :=
  ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
    Etale ψ ∧ Surjective ψ ∧
      ∀ {W : AlgebraicSpace S} {pV : W ⟶ ofOver V} {pX : W ⟶ X},
        IsPullback pV pX ψ f → Decent pV

/-- `existsEtaleOnTarget f` is the existence of a surjective étale scheme atlas
of `Y` along which pullbacks of `f` are decent. -/
theorem existsEtaleOnTarget_iff : existsEtaleOnTarget f ↔
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ (W : AlgebraicSpace S) (pV : W ⟶ ofOver V) (pX : W ⟶ X),
          IsPullback pV pX ψ f → Decent pV := sorry

namespace existsEtaleOnTarget

/-- A surjective étale scheme atlas of `Y` with decent pullbacks of `f`
witnesses `existsEtaleOnTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ {W : AlgebraicSpace S} {pV : W ⟶ ofOver V} {pX : W ⟶ X},
      IsPullback pV pX ψ f → Decent pV) :
    existsEtaleOnTarget f := sorry

/-- `existsEtaleOnTarget f` supplies a surjective étale scheme atlas of `Y`
along which pullbacks of `f` are decent. -/
theorem spec (h : existsEtaleOnTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ {W : AlgebraicSpace S} {pV : W ⟶ ofOver V} {pX : W ⟶ X},
          IsPullback pV pX ψ f → Decent pV := sorry

end existsEtaleOnTarget

end Decent

namespace Reasonable

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- The projection of every affine-scheme-valued base change of `f` is
reasonable. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {W : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
    IsPullback pZ pX g f → Reasonable pZ

/-- `forallAffine f` means every affine-scheme-valued pullback projection of `f`
is reasonable. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (W : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : W ⟶ ofOver Z) (pX : W ⟶ X),
      IsPullback pZ pX g f → Reasonable pZ := sorry

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses
`forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {W : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
    IsPullback pZ pX g f → Reasonable pZ) : forallAffine f := sorry

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is reasonable. -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {W : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z}
    {pX : W ⟶ X} (sq : IsPullback pZ pX g f) : Reasonable pZ := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme is reasonable whenever `forallAffine f` holds. -/
theorem pullback_snd {Z : Over S} [IsAffine Z.left] (h : forallAffine f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] : Reasonable (pullback.snd f g) := sorry

end forallAffine

/-- Every affine-scheme-valued pullback of the source of `f` is reasonable as an
algebraic space. -/
def forallAffineObject : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {W : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
    IsPullback pZ pX g f → IsReasonable W

/-- `forallAffineObject f` means every affine-scheme-valued pullback of the
source of `f` is reasonable. -/
theorem forallAffineObject_iff : forallAffineObject f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (W : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : W ⟶ ofOver Z) (pX : W ⟶ X),
      IsPullback pZ pX g f → IsReasonable W := sorry

namespace forallAffineObject

/-- A universal affine-scheme-valued pullback condition on the source witnesses
`forallAffineObject f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {W : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
    IsPullback pZ pX g f → IsReasonable W) : forallAffineObject f := sorry

/-- Under `forallAffineObject f`, the vertex of any affine-scheme-valued
pullback of `f` is reasonable. -/
theorem spec (h : forallAffineObject f) {Z : Over S} [IsAffine Z.left]
    {W : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z}
    {pX : W ⟶ X} (sq : IsPullback pZ pX g f) : IsReasonable W := sorry

/-- The chosen pullback `pullback f g` along a morphism from an affine scheme is
reasonable whenever `forallAffineObject f` holds. -/
theorem pullback {Z : Over S} [IsAffine Z.left] (h : forallAffineObject f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] : IsReasonable (Limits.pullback f g) := sorry

end forallAffineObject

/-- There is a Zariski covering of `Y` along which every inverse-image
projection of `f` is reasonable. -/
def existsZariskiCover : Prop :=
  ∃ (𝒰 : ZariskiCover.{u, u} Y),
    ∀ i {W : AlgebraicSpace S} {pYi : W ⟶ 𝒰.X i} {pX : W ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → Reasonable pYi

/-- `existsZariskiCover f` is the existence of a Zariski covering of `Y` whose
inverse images under `f` are reasonable over the covering opens. -/
theorem existsZariskiCover_iff : existsZariskiCover f ↔
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i (W : AlgebraicSpace S) (pYi : W ⟶ 𝒰.X i) (pX : W ⟶ X),
        IsPullback pYi pX (𝒰.f i) f → Reasonable pYi := sorry

namespace existsZariskiCover

/-- A Zariski covering of `Y` with reasonable inverse-image projections of `f`
witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {W : AlgebraicSpace S} {pYi : W ⟶ 𝒰.X i} {pX : W ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → Reasonable pYi) :
    existsZariskiCover f := sorry

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` are reasonable over the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {W : AlgebraicSpace S} {pYi : W ⟶ 𝒰.X i} {pX : W ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → Reasonable pYi := sorry

end existsZariskiCover

/-- There is a surjective étale morphism from a scheme to `Y` along which every
pullback of `f` is reasonable. -/
def existsEtaleOnTarget : Prop :=
  ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
    Etale ψ ∧ Surjective ψ ∧
      ∀ {W : AlgebraicSpace S} {pV : W ⟶ ofOver V} {pX : W ⟶ X},
        IsPullback pV pX ψ f → Reasonable pV

/-- `existsEtaleOnTarget f` is the existence of a surjective étale scheme atlas
of `Y` along which pullbacks of `f` are reasonable. -/
theorem existsEtaleOnTarget_iff : existsEtaleOnTarget f ↔
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ (W : AlgebraicSpace S) (pV : W ⟶ ofOver V) (pX : W ⟶ X),
          IsPullback pV pX ψ f → Reasonable pV := sorry

namespace existsEtaleOnTarget

/-- A surjective étale scheme atlas of `Y` with reasonable pullbacks of `f`
witnesses `existsEtaleOnTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ {W : AlgebraicSpace S} {pV : W ⟶ ofOver V} {pX : W ⟶ X},
      IsPullback pV pX ψ f → Reasonable pV) :
    existsEtaleOnTarget f := sorry

/-- `existsEtaleOnTarget f` supplies a surjective étale scheme atlas of `Y`
along which pullbacks of `f` are reasonable. -/
theorem spec (h : existsEtaleOnTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ {W : AlgebraicSpace S} {pV : W ⟶ ofOver V} {pX : W ⟶ X},
          IsPullback pV pX ψ f → Reasonable pV := sorry

end existsEtaleOnTarget

end Reasonable

namespace VeryReasonable

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- The projection of every affine-scheme-valued base change of `f` is
very reasonable. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {W : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
    IsPullback pZ pX g f → VeryReasonable pZ

/-- `forallAffine f` means every affine-scheme-valued pullback projection of `f`
is very reasonable. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (W : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : W ⟶ ofOver Z) (pX : W ⟶ X),
      IsPullback pZ pX g f → VeryReasonable pZ := sorry

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses
`forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {W : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
    IsPullback pZ pX g f → VeryReasonable pZ) : forallAffine f := sorry

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is very reasonable. -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {W : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z}
    {pX : W ⟶ X} (sq : IsPullback pZ pX g f) : VeryReasonable pZ := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme is very reasonable whenever `forallAffine f` holds. -/
theorem pullback_snd {Z : Over S} [IsAffine Z.left] (h : forallAffine f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] : VeryReasonable (pullback.snd f g) := sorry

end forallAffine

/-- Every affine-scheme-valued pullback of the source of `f` is very reasonable as an
algebraic space. -/
def forallAffineObject : Prop :=
  ∀ {Z : Over S} [IsAffine Z.left] {W : AlgebraicSpace S} {g : ofOver Z ⟶ Y}
    {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
    IsPullback pZ pX g f → IsVeryReasonable W

/-- `forallAffineObject f` means every affine-scheme-valued pullback of the
source of `f` is very reasonable. -/
theorem forallAffineObject_iff : forallAffineObject f ↔
    ∀ (Z : Over S) [IsAffine Z.left] (W : AlgebraicSpace S) (g : ofOver Z ⟶ Y)
      (pZ : W ⟶ ofOver Z) (pX : W ⟶ X),
      IsPullback pZ pX g f → IsVeryReasonable W := sorry

namespace forallAffineObject

/-- A universal affine-scheme-valued pullback condition on the source witnesses
`forallAffineObject f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {W : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
    IsPullback pZ pX g f → IsVeryReasonable W) : forallAffineObject f := sorry

/-- Under `forallAffineObject f`, the vertex of any affine-scheme-valued
pullback of `f` is very reasonable. -/
theorem spec (h : forallAffineObject f) {Z : Over S} [IsAffine Z.left]
    {W : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z}
    {pX : W ⟶ X} (sq : IsPullback pZ pX g f) : IsVeryReasonable W := sorry

/-- The chosen pullback `pullback f g` along a morphism from an affine scheme is
very reasonable whenever `forallAffineObject f` holds. -/
theorem pullback {Z : Over S} [IsAffine Z.left] (h : forallAffineObject f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] : IsVeryReasonable (Limits.pullback f g) := sorry

end forallAffineObject

/-- There is a Zariski covering of `Y` along which every inverse-image
projection of `f` is very reasonable. -/
def existsZariskiCover : Prop :=
  ∃ (𝒰 : ZariskiCover.{u, u} Y),
    ∀ i {W : AlgebraicSpace S} {pYi : W ⟶ 𝒰.X i} {pX : W ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → VeryReasonable pYi

/-- `existsZariskiCover f` is the existence of a Zariski covering of `Y` whose
inverse images under `f` are very reasonable over the covering opens. -/
theorem existsZariskiCover_iff : existsZariskiCover f ↔
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i (W : AlgebraicSpace S) (pYi : W ⟶ 𝒰.X i) (pX : W ⟶ X),
        IsPullback pYi pX (𝒰.f i) f → VeryReasonable pYi := sorry

namespace existsZariskiCover

/-- A Zariski covering of `Y` with very reasonable inverse-image projections of `f`
witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {W : AlgebraicSpace S} {pYi : W ⟶ 𝒰.X i} {pX : W ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → VeryReasonable pYi) :
    existsZariskiCover f := sorry

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` are very reasonable over the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {W : AlgebraicSpace S} {pYi : W ⟶ 𝒰.X i} {pX : W ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → VeryReasonable pYi := sorry

end existsZariskiCover

end VeryReasonable

end AlgebraicGeometry.AlgebraicSpace
