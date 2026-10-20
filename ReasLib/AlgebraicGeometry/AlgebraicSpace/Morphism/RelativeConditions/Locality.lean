/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.RelativeConditions
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.VeryReasonable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.ZariskiCover.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective

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
      IsPullback pZ pX g f → PropertyBeta pZ := by
  constructor
  · intro h Z hZ W g pZ pX sq
    exact h sq
  · intro h Z hZ W g pZ pX sq
    exact h Z W g pZ pX sq

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses
`forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {W : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
    IsPullback pZ pX g f → PropertyBeta pZ) : forallAffine f := h

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` has property (β). -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {W : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z}
    {pX : W ⟶ X} (sq : IsPullback pZ pX g f) : PropertyBeta pZ := h sq

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme has property (β) whenever `forallAffine f` holds. -/
theorem pullback_snd {Z : Over S} [IsAffine Z.left] (h : forallAffine f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] : PropertyBeta (pullback.snd f g) := h (IsPullback.of_hasPullback f g).flip

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
      IsPullback pZ pX g f → HasPropertyBeta W := by
  constructor
  · intro h Z hZ W g pZ pX sq
    exact h sq
  · intro h Z hZ W g pZ pX sq
    exact h Z W g pZ pX sq

namespace forallAffineObject

/-- A universal affine-scheme-valued pullback condition on the source witnesses
`forallAffineObject f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {W : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
    IsPullback pZ pX g f → HasPropertyBeta W) : forallAffineObject f := h

/-- Under `forallAffineObject f`, the vertex of any affine-scheme-valued
pullback of `f` has property (β). -/
theorem spec (h : forallAffineObject f) {Z : Over S} [IsAffine Z.left]
    {W : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z}
    {pX : W ⟶ X} (sq : IsPullback pZ pX g f) : HasPropertyBeta W := h sq

/-- The chosen pullback `pullback f g` along a morphism from an affine scheme is
property (β) whenever `forallAffineObject f` holds. -/
theorem pullback {Z : Over S} [IsAffine Z.left] (h : forallAffineObject f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] : HasPropertyBeta (Limits.pullback f g) := h (IsPullback.of_hasPullback f g).flip

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
        IsPullback pYi pX (𝒰.f i) f → PropertyBeta pYi := by
  constructor
  · rintro ⟨𝒰, h⟩
    exact ⟨𝒰, fun i W pYi pX sq => h i sq⟩
  · rintro ⟨𝒰, h⟩
    refine ⟨𝒰, ?_⟩
    intro i W pYi pX sq
    exact h i W pYi pX sq

namespace existsZariskiCover

/-- A Zariski covering of `Y` with inverse-image projections of `f` having
property (β) witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {W : AlgebraicSpace S} {pYi : W ⟶ 𝒰.X i} {pX : W ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → PropertyBeta pYi) :
    existsZariskiCover f := ⟨𝒰, h⟩

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` have property (β) over the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {W : AlgebraicSpace S} {pYi : W ⟶ 𝒰.X i} {pX : W ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → PropertyBeta pYi := h

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
          IsPullback pV pX ψ f → PropertyBeta pV := by
  constructor
  · rintro ⟨V, ψ, hEtale, hSurj, h⟩
    exact ⟨V, ψ, hEtale, hSurj, fun W pV pX sq => h sq⟩
  · rintro ⟨V, ψ, hEtale, hSurj, h⟩
    refine ⟨V, ψ, hEtale, hSurj, ?_⟩
    intro W pV pX sq
    exact h W pV pX sq

namespace existsEtaleOnTarget

/-- A surjective étale scheme atlas of `Y` with pullbacks of `f` having property (β)
witnesses `existsEtaleOnTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ {W : AlgebraicSpace S} {pV : W ⟶ ofOver V} {pX : W ⟶ X},
      IsPullback pV pX ψ f → PropertyBeta pV) :
    existsEtaleOnTarget f := ⟨V, ψ, inferInstance, inferInstance, h⟩

/-- `existsEtaleOnTarget f` supplies a surjective étale scheme atlas of `Y`
along which pullbacks of `f` have property (β). -/
theorem spec (h : existsEtaleOnTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ {W : AlgebraicSpace S} {pV : W ⟶ ofOver V} {pX : W ⟶ X},
          IsPullback pV pX ψ f → PropertyBeta pV := h

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
      IsPullback pZ pX g f → Decent pZ := by
  constructor
  · intro h Z hZ W g pZ pX sq
    exact h sq
  · intro h Z hZ W g pZ pX sq
    exact h Z W g pZ pX sq

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses
`forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {W : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
    IsPullback pZ pX g f → Decent pZ) : forallAffine f := h

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is decent. -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {W : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z}
    {pX : W ⟶ X} (sq : IsPullback pZ pX g f) : Decent pZ := h sq

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme is decent whenever `forallAffine f` holds. -/
theorem pullback_snd {Z : Over S} [IsAffine Z.left] (h : forallAffine f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] : Decent (pullback.snd f g) := h (IsPullback.of_hasPullback f g).flip

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
      IsPullback pZ pX g f → IsDecent W := by
  constructor
  · intro h Z hZ W g pZ pX sq
    exact h sq
  · intro h Z hZ W g pZ pX sq
    exact h Z W g pZ pX sq

namespace forallAffineObject

/-- A universal affine-scheme-valued pullback condition on the source witnesses
`forallAffineObject f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {W : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
    IsPullback pZ pX g f → IsDecent W) : forallAffineObject f := h

/-- Under `forallAffineObject f`, the vertex of any affine-scheme-valued
pullback of `f` is decent. -/
theorem spec (h : forallAffineObject f) {Z : Over S} [IsAffine Z.left]
    {W : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z}
    {pX : W ⟶ X} (sq : IsPullback pZ pX g f) : IsDecent W := h sq

/-- The chosen pullback `pullback f g` along a morphism from an affine scheme is
decent whenever `forallAffineObject f` holds. -/
theorem pullback {Z : Over S} [IsAffine Z.left] (h : forallAffineObject f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] : IsDecent (Limits.pullback f g) := h (IsPullback.of_hasPullback f g).flip

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
        IsPullback pYi pX (𝒰.f i) f → Decent pYi := by
  constructor
  · rintro ⟨𝒰, h⟩
    exact ⟨𝒰, fun i W pYi pX sq => h i sq⟩
  · rintro ⟨𝒰, h⟩
    refine ⟨𝒰, ?_⟩
    intro i W pYi pX sq
    exact h i W pYi pX sq

namespace existsZariskiCover

/-- A Zariski covering of `Y` with decent inverse-image projections of `f`
witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {W : AlgebraicSpace S} {pYi : W ⟶ 𝒰.X i} {pX : W ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → Decent pYi) :
    existsZariskiCover f := ⟨𝒰, h⟩

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` are decent over the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {W : AlgebraicSpace S} {pYi : W ⟶ 𝒰.X i} {pX : W ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → Decent pYi := h

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
          IsPullback pV pX ψ f → Decent pV := by
  constructor
  · rintro ⟨V, ψ, hEtale, hSurj, h⟩
    exact ⟨V, ψ, hEtale, hSurj, fun W pV pX sq => h sq⟩
  · rintro ⟨V, ψ, hEtale, hSurj, h⟩
    refine ⟨V, ψ, hEtale, hSurj, ?_⟩
    intro W pV pX sq
    exact h W pV pX sq

namespace existsEtaleOnTarget

/-- A surjective étale scheme atlas of `Y` with decent pullbacks of `f`
witnesses `existsEtaleOnTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ {W : AlgebraicSpace S} {pV : W ⟶ ofOver V} {pX : W ⟶ X},
      IsPullback pV pX ψ f → Decent pV) :
    existsEtaleOnTarget f := ⟨V, ψ, inferInstance, inferInstance, h⟩

/-- `existsEtaleOnTarget f` supplies a surjective étale scheme atlas of `Y`
along which pullbacks of `f` are decent. -/
theorem spec (h : existsEtaleOnTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ {W : AlgebraicSpace S} {pV : W ⟶ ofOver V} {pX : W ⟶ X},
          IsPullback pV pX ψ f → Decent pV := h

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
      IsPullback pZ pX g f → Reasonable pZ := by
  constructor
  · intro h Z hZ W g pZ pX sq
    exact h sq
  · intro h Z hZ W g pZ pX sq
    exact h Z W g pZ pX sq

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses
`forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {W : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
    IsPullback pZ pX g f → Reasonable pZ) : forallAffine f := h

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is reasonable. -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {W : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z}
    {pX : W ⟶ X} (sq : IsPullback pZ pX g f) : Reasonable pZ := h sq

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme is reasonable whenever `forallAffine f` holds. -/
theorem pullback_snd {Z : Over S} [IsAffine Z.left] (h : forallAffine f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] : Reasonable (pullback.snd f g) := h (IsPullback.of_hasPullback f g).flip

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
      IsPullback pZ pX g f → IsReasonable W := by
  constructor
  · intro h Z hZ W g pZ pX sq
    exact h sq
  · intro h Z hZ W g pZ pX sq
    exact h Z W g pZ pX sq

namespace forallAffineObject

/-- A universal affine-scheme-valued pullback condition on the source witnesses
`forallAffineObject f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {W : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
    IsPullback pZ pX g f → IsReasonable W) : forallAffineObject f := h

/-- Under `forallAffineObject f`, the vertex of any affine-scheme-valued
pullback of `f` is reasonable. -/
theorem spec (h : forallAffineObject f) {Z : Over S} [IsAffine Z.left]
    {W : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z}
    {pX : W ⟶ X} (sq : IsPullback pZ pX g f) : IsReasonable W := h sq

/-- The chosen pullback `pullback f g` along a morphism from an affine scheme is
reasonable whenever `forallAffineObject f` holds. -/
theorem pullback {Z : Over S} [IsAffine Z.left] (h : forallAffineObject f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] : IsReasonable (Limits.pullback f g) := h (IsPullback.of_hasPullback f g).flip

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
        IsPullback pYi pX (𝒰.f i) f → Reasonable pYi := by
  constructor
  · rintro ⟨𝒰, h⟩
    exact ⟨𝒰, fun i W pYi pX sq => h i sq⟩
  · rintro ⟨𝒰, h⟩
    refine ⟨𝒰, ?_⟩
    intro i W pYi pX sq
    exact h i W pYi pX sq

namespace existsZariskiCover

/-- A Zariski covering of `Y` with reasonable inverse-image projections of `f`
witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {W : AlgebraicSpace S} {pYi : W ⟶ 𝒰.X i} {pX : W ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → Reasonable pYi) :
    existsZariskiCover f := ⟨𝒰, h⟩

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` are reasonable over the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {W : AlgebraicSpace S} {pYi : W ⟶ 𝒰.X i} {pX : W ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → Reasonable pYi := h

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
          IsPullback pV pX ψ f → Reasonable pV := by
  constructor
  · rintro ⟨V, ψ, hEtale, hSurj, h⟩
    exact ⟨V, ψ, hEtale, hSurj, fun W pV pX sq => h sq⟩
  · rintro ⟨V, ψ, hEtale, hSurj, h⟩
    refine ⟨V, ψ, hEtale, hSurj, ?_⟩
    intro W pV pX sq
    exact h W pV pX sq

namespace existsEtaleOnTarget

/-- A surjective étale scheme atlas of `Y` with reasonable pullbacks of `f`
witnesses `existsEtaleOnTarget f`. -/
theorem of {V : Over S} (ψ : ofOver V ⟶ Y) [Etale ψ] [Surjective ψ]
    (h : ∀ {W : AlgebraicSpace S} {pV : W ⟶ ofOver V} {pX : W ⟶ X},
      IsPullback pV pX ψ f → Reasonable pV) :
    existsEtaleOnTarget f := ⟨V, ψ, inferInstance, inferInstance, h⟩

/-- `existsEtaleOnTarget f` supplies a surjective étale scheme atlas of `Y`
along which pullbacks of `f` are reasonable. -/
theorem spec (h : existsEtaleOnTarget f) :
    ∃ (V : Over S) (ψ : ofOver V ⟶ Y),
      Etale ψ ∧ Surjective ψ ∧
        ∀ {W : AlgebraicSpace S} {pV : W ⟶ ofOver V} {pX : W ⟶ X},
          IsPullback pV pX ψ f → Reasonable pV := h

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
      IsPullback pZ pX g f → VeryReasonable pZ := by
  constructor
  · intro h Z hZ W g pZ pX sq
    exact h sq
  · intro h Z hZ W g pZ pX sq
    exact h Z W g pZ pX sq

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses
`forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {W : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
    IsPullback pZ pX g f → VeryReasonable pZ) : forallAffine f := h

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is very reasonable. -/
theorem spec (h : forallAffine f) {Z : Over S} [IsAffine Z.left]
    {W : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z}
    {pX : W ⟶ X} (sq : IsPullback pZ pX g f) : VeryReasonable pZ := h sq

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme is very reasonable whenever `forallAffine f` holds. -/
theorem pullback_snd {Z : Over S} [IsAffine Z.left] (h : forallAffine f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] : VeryReasonable (pullback.snd f g) := h (IsPullback.of_hasPullback f g).flip

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
      IsPullback pZ pX g f → IsVeryReasonable W := by
  constructor
  · intro h Z hZ W g pZ pX sq
    exact h sq
  · intro h Z hZ W g pZ pX sq
    exact h Z W g pZ pX sq

namespace forallAffineObject

/-- A universal affine-scheme-valued pullback condition on the source witnesses
`forallAffineObject f`. -/
theorem of (h : ∀ {Z : Over S} [IsAffine Z.left] {W : AlgebraicSpace S}
    {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z} {pX : W ⟶ X},
    IsPullback pZ pX g f → IsVeryReasonable W) : forallAffineObject f := h

/-- Under `forallAffineObject f`, the vertex of any affine-scheme-valued
pullback of `f` is very reasonable. -/
theorem spec (h : forallAffineObject f) {Z : Over S} [IsAffine Z.left]
    {W : AlgebraicSpace S} {g : ofOver Z ⟶ Y} {pZ : W ⟶ ofOver Z}
    {pX : W ⟶ X} (sq : IsPullback pZ pX g f) : IsVeryReasonable W := h sq

/-- The chosen pullback `pullback f g` along a morphism from an affine scheme is
very reasonable whenever `forallAffineObject f` holds. -/
theorem pullback {Z : Over S} [IsAffine Z.left] (h : forallAffineObject f)
    (g : ofOver Z ⟶ Y) [HasPullback f g] : IsVeryReasonable (Limits.pullback f g) := h (IsPullback.of_hasPullback f g).flip

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
        IsPullback pYi pX (𝒰.f i) f → VeryReasonable pYi := by
  constructor
  · rintro ⟨𝒰, h⟩
    exact ⟨𝒰, fun i W pYi pX sq => h i sq⟩
  · rintro ⟨𝒰, h⟩
    refine ⟨𝒰, ?_⟩
    intro i W pYi pX sq
    exact h i W pYi pX sq

namespace existsZariskiCover

/-- A Zariski covering of `Y` with very reasonable inverse-image projections of `f`
witnesses `existsZariskiCover f`. -/
theorem of (𝒰 : ZariskiCover.{u, u} Y)
    (h : ∀ i {W : AlgebraicSpace S} {pYi : W ⟶ 𝒰.X i} {pX : W ⟶ X},
      IsPullback pYi pX (𝒰.f i) f → VeryReasonable pYi) :
    existsZariskiCover f := ⟨𝒰, h⟩

/-- `existsZariskiCover f` supplies a Zariski covering of `Y` whose inverse
images under `f` are very reasonable over the covering opens. -/
theorem spec (h : existsZariskiCover f) :
    ∃ (𝒰 : ZariskiCover.{u, u} Y),
      ∀ i {W : AlgebraicSpace S} {pYi : W ⟶ 𝒰.X i} {pX : W ⟶ X},
        IsPullback pYi pX (𝒰.f i) f → VeryReasonable pYi := h

end existsZariskiCover

end VeryReasonable


namespace PropertyBeta

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the following are equivalent: `PropertyBeta f`; every affine-scheme-valued
base change of `f` has property (β); every such pullback space has property (β);
some Zariski covering of `Y` has each inverse-image projection `f⁻¹(Yᵢ) ⟶ Yᵢ`
with property (β); and some surjective étale scheme atlas of `Y` has pullback of
`f` with property (β). -/
theorem tfae :
    List.TFAE [PropertyBeta f, forallAffine f, forallAffineObject f, existsZariskiCover f,
      existsEtaleOnTarget f] := sorry

/-- A morphism of algebraic spaces has property (β) iff every affine-scheme-valued
base change has property (β). -/
theorem iff_forallAffine : PropertyBeta f ↔ forallAffine f := (tfae f).out 0 1

/-- A morphism of algebraic spaces has property (β) iff every affine-scheme-valued
pullback of its source has property (β). -/
theorem iff_forallAffineObject : PropertyBeta f ↔ forallAffineObject f := (tfae f).out 0 2

/-- A morphism of algebraic spaces has property (β) iff some Zariski covering of
the target has inverse images under `f` with property (β). -/
theorem iff_existsZariskiCover : PropertyBeta f ↔ existsZariskiCover f := (tfae f).out 0 3

/-- A morphism of algebraic spaces has property (β) iff some surjective étale
scheme atlas of the target has pullback of `f` with property (β). -/
theorem iff_existsEtaleOnTarget : PropertyBeta f ↔ existsEtaleOnTarget f := (tfae f).out 0 4

end PropertyBeta

namespace Decent

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the following are equivalent: `Decent f`; every affine-scheme-valued base
change of `f` is decent; every such pullback space is decent; some Zariski
covering of `Y` has each inverse-image projection `f⁻¹(Yᵢ) ⟶ Yᵢ` decent; and
some surjective étale scheme atlas of `Y` has decent pullback of `f`. -/
theorem tfae :
    List.TFAE [Decent f, forallAffine f, forallAffineObject f, existsZariskiCover f,
      existsEtaleOnTarget f] := sorry

/-- A morphism of algebraic spaces is decent iff every affine-scheme-valued base
change is decent. -/
theorem iff_forallAffine : Decent f ↔ forallAffine f := (tfae f).out 0 1

/-- A morphism of algebraic spaces is decent iff every affine-scheme-valued
pullback of its source is decent. -/
theorem iff_forallAffineObject : Decent f ↔ forallAffineObject f := (tfae f).out 0 2

/-- A morphism of algebraic spaces is decent iff some Zariski covering of the
target has decent inverse images under `f`. -/
theorem iff_existsZariskiCover : Decent f ↔ existsZariskiCover f := (tfae f).out 0 3

/-- A morphism of algebraic spaces is decent iff some surjective étale scheme
atlas of the target has decent pullback of `f`. -/
theorem iff_existsEtaleOnTarget : Decent f ↔ existsEtaleOnTarget f := (tfae f).out 0 4

end Decent

namespace Reasonable

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the following are equivalent: `Reasonable f`; every affine-scheme-valued
base change of `f` is reasonable; every such pullback space is reasonable; some
Zariski covering of `Y` has each inverse-image projection `f⁻¹(Yᵢ) ⟶ Yᵢ`
reasonable; and some surjective étale scheme atlas of `Y` has reasonable
pullback of `f`. -/
theorem tfae :
    List.TFAE [Reasonable f, forallAffine f, forallAffineObject f, existsZariskiCover f,
      existsEtaleOnTarget f] := sorry

/-- A morphism of algebraic spaces is reasonable iff every affine-scheme-valued
base change is reasonable. -/
theorem iff_forallAffine : Reasonable f ↔ forallAffine f := (tfae f).out 0 1

/-- A morphism of algebraic spaces is reasonable iff every affine-scheme-valued
pullback of its source is reasonable. -/
theorem iff_forallAffineObject : Reasonable f ↔ forallAffineObject f := (tfae f).out 0 2

/-- A morphism of algebraic spaces is reasonable iff some Zariski covering of the
target has reasonable inverse images under `f`. -/
theorem iff_existsZariskiCover : Reasonable f ↔ existsZariskiCover f := (tfae f).out 0 3

/-- A morphism of algebraic spaces is reasonable iff some surjective étale scheme
atlas of the target has reasonable pullback of `f`. -/
theorem iff_existsEtaleOnTarget : Reasonable f ↔ existsEtaleOnTarget f := (tfae f).out 0 4

end Reasonable

namespace VeryReasonable

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)

/-- For a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S`, the following are equivalent: `VeryReasonable f`; every affine-scheme-valued
base change of `f` is very reasonable; every such pullback space is very
reasonable; and some Zariski covering of `Y` has each inverse-image projection
`f⁻¹(Yᵢ) ⟶ Yᵢ` very reasonable. -/
theorem tfae :
    List.TFAE [VeryReasonable f, forallAffine f, forallAffineObject f,
      existsZariskiCover f] := sorry

/-- A morphism of algebraic spaces is very reasonable iff every
affine-scheme-valued base change is very reasonable. -/
theorem iff_forallAffine : VeryReasonable f ↔ forallAffine f := (tfae f).out 0 1

/-- A morphism of algebraic spaces is very reasonable iff every
affine-scheme-valued pullback of its source is very reasonable. -/
theorem iff_forallAffineObject : VeryReasonable f ↔ forallAffineObject f := (tfae f).out 0 2

/-- A morphism of algebraic spaces is very reasonable iff some Zariski covering
of the target has very reasonable inverse images under `f`. -/
theorem iff_existsZariskiCover : VeryReasonable f ↔ existsZariskiCover f := (tfae f).out 0 3

end VeryReasonable

end AlgebraicGeometry.AlgebraicSpace
