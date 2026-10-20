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
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Basic
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Separation
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Reduction
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Morphism.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation.Absolute

/-!
# Local tests for separation of morphisms of formal algebraic spaces

Separatedness and quasi-separatedness are equivalent to their scheme and affine
base-change tests, absolute separation of the reductions of affine pullbacks,
and the corresponding property on an affine formal étale atlas of the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace

namespace Separated

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y)

/-- The projection of every scheme-valued base change of `f` is separated. -/
def forallScheme : Prop :=
  ∀ {Z : Over S} {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Separated pZ

/-- `forallScheme f` means every scheme-valued pullback projection of `f` is
separated. -/
theorem forallScheme_iff : forallScheme f ↔
    ∀ (Z : Over S) (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj Z ⟶ Y)
      (pZ : P ⟶ yoneda.obj Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → Separated pZ := by
  constructor
  · intro h Z P g pZ pX sq
    exact h sq
  · intro h Z P g pZ pX sq
    exact h Z P g pZ pX sq

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Separated pZ) : forallScheme f := by
  exact h

/-- Under `forallScheme f`, the test-leg of any scheme-valued pullback of `f` is
separated. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Separated pZ := by
  exact h sq

/-- The chosen pullback projection `pullback.snd f g` along a morphism from a
scheme is separated whenever `forallScheme f` holds. -/
theorem pullback_snd {Z : Over S} (h : forallScheme f) (g : yoneda.obj Z ⟶ Y)
    [HasPullback f g] : Separated (pullback.snd f g) := by
  exact h (IsPullback.of_hasPullback f g).flip

end forallScheme

/-- The projection of every affine-scheme-valued base change of `f` is
separated. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left] {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Separated pZ

/-- `forallAffine f` means every affine-scheme-valued pullback projection of `f`
is separated. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [AlgebraicGeometry.IsAffine Z.left]
      (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj Z ⟶ Y)
      (pZ : P ⟶ yoneda.obj Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → Separated pZ := by
  constructor
  · intro h Z hZ P g pZ pX sq
    exact h sq
  · intro h Z hZ P g pZ pX sq
    exact h Z P g pZ pX sq

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses
`forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → Separated pZ) : forallAffine f := by
  exact h

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is separated. -/
theorem spec (h : forallAffine f) {Z : Over S}
    [AlgebraicGeometry.IsAffine Z.left] {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : Separated pZ := by
  exact h sq

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme is separated whenever `forallAffine f` holds. -/
theorem pullback_snd {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    (h : forallAffine f) (g : yoneda.obj Z ⟶ Y) [HasPullback f g] :
    Separated (pullback.snd f g) := by
  exact h (IsPullback.of_hasPullback f g).flip

end forallAffine

/-- Every affine-scheme-valued fibre product of `f` is a separated formal
algebraic space: every reduction is an absolutely separated algebraic space. -/
def forallAffineSpace : Prop :=
  ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    [IsFormalAlgebraicSpace P] (R : ReductionData P),
    IsPullback pZ pX g f → AlgebraicSpace.IsAbsolutelySeparated R.space

/-- `forallAffineSpace f` means every affine-scheme-valued fibre product of `f`
has absolutely separated reduction. -/
theorem forallAffineSpace_iff : forallAffineSpace f ↔
    ∀ (Z : Over S) [AlgebraicGeometry.IsAffine Z.left]
      (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj Z ⟶ Y)
      (pZ : P ⟶ yoneda.obj Z) (pX : P ⟶ X)
      [IsFormalAlgebraicSpace P] (R : ReductionData P),
      IsPullback pZ pX g f →
        AlgebraicSpace.IsAbsolutelySeparated R.space := by
  constructor
  · intro h Z hZ P g pZ pX hP R sq
    exact h R sq
  · intro h Z hZ P g pZ pX hP R sq
    exact h Z P g pZ pX R sq

namespace forallAffineSpace

/-- Affine-scheme-valued fibre products whose reductions are absolutely
separated witness `forallAffineSpace f`. -/
theorem of (h : ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    [IsFormalAlgebraicSpace P] (R : ReductionData P),
    IsPullback pZ pX g f →
      AlgebraicSpace.IsAbsolutelySeparated R.space) :
    forallAffineSpace f := by
  exact h

/-- Under `forallAffineSpace f`, the reduction of any affine-scheme-valued
fibre product of `f` is absolutely separated. -/
theorem spec (h : forallAffineSpace f) {Z : Over S}
    [AlgebraicGeometry.IsAffine Z.left] {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    [IsFormalAlgebraicSpace P] (R : ReductionData P)
    (sq : IsPullback pZ pX g f) :
    AlgebraicSpace.IsAbsolutelySeparated R.space := by
  exact h R sq

/-- The reduction of the chosen fibre product along a morphism from an affine
scheme is absolutely separated whenever `forallAffineSpace f` holds. -/
theorem pullback_snd {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    (h : forallAffineSpace f) (g : yoneda.obj Z ⟶ Y) [HasPullback f g]
    [IsFormalAlgebraicSpace (pullback f g)] (R : ReductionData (pullback f g)) :
    AlgebraicSpace.IsAbsolutelySeparated R.space := by
  exact h R (IsPullback.of_hasPullback f g).flip

end forallAffineSpace

/-- There is a jointly fppf-locally surjective étale covering of `Y` by affine
formal algebraic spaces, along which every pullback
of `f` is separated. -/
def existsCoverOnTarget : Prop :=
  ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
    (∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j)) ∧
      (∀ j, Etale (π j)) ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) ∧
          (∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
            IsPullback pY pX (π j) f → Separated pY)

/-- `existsCoverOnTarget f` is the existence of an affine formal étale atlas of
`Y` along which pullbacks of `f` are separated. -/
theorem existsCoverOnTarget_iff : existsCoverOnTarget f ↔
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
      (∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j)) ∧
        (∀ j, Etale (π j)) ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
            (sigmaDesc π) ∧
            (∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
              IsPullback pY pX (π j) f → Separated pY) := Iff.rfl

namespace existsCoverOnTarget

/-- An affine formal étale atlas of `Y` with separated pullbacks of `f` witnesses
`existsCoverOnTarget f`. -/
theorem of {ι : Type u} {Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    (π : (j : ι) → Y_ j ⟶ Y)
    (hAffine : ∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j))
    (hEtale : ∀ j, Etale (π j))
    (hCover : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (sigmaDesc π))
    (hSep : ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
      IsPullback pY pX (π j) f → Separated pY) :
    existsCoverOnTarget f := by
  exact ⟨ι, Y_, π, hAffine, hEtale, hCover, hSep⟩

/-- `existsCoverOnTarget f` supplies an affine formal étale atlas of `Y` along
which pullbacks of `f` are separated. -/
theorem spec (h : existsCoverOnTarget f) :
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
      (∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j)) ∧
        (∀ j, Etale (π j)) ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
            (sigmaDesc π) ∧
            (∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
              IsPullback pY pX (π j) f → Separated pY) := by
  exact h

end existsCoverOnTarget

end Separated

namespace QuasiSeparated

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y)

/-- The projection of every scheme-valued base change of `f` is
quasi-separated. -/
def forallScheme : Prop :=
  ∀ {Z : Over S} {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → QuasiSeparated pZ

/-- `forallScheme f` means every scheme-valued pullback projection of `f` is
quasi-separated. -/
theorem forallScheme_iff : forallScheme f ↔
    ∀ (Z : Over S) (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj Z ⟶ Y)
      (pZ : P ⟶ yoneda.obj Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → QuasiSeparated pZ := by
  constructor
  · intro h Z P g pZ pX sq
    exact h sq
  · intro h Z P g pZ pX sq
    exact h Z P g pZ pX sq

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → QuasiSeparated pZ) : forallScheme f := by
  exact h

/-- Under `forallScheme f`, the test-leg of any scheme-valued pullback of `f` is
quasi-separated. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : QuasiSeparated pZ := by
  exact h sq

/-- The chosen pullback projection `pullback.snd f g` along a morphism from a
scheme is quasi-separated whenever `forallScheme f` holds. -/
theorem pullback_snd {Z : Over S} (h : forallScheme f) (g : yoneda.obj Z ⟶ Y)
    [HasPullback f g] : QuasiSeparated (pullback.snd f g) := by
  exact h (IsPullback.of_hasPullback f g).flip

end forallScheme

/-- The projection of every affine-scheme-valued base change of `f` is
quasi-separated. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left] {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → QuasiSeparated pZ

/-- `forallAffine f` means every affine-scheme-valued pullback projection of `f`
is quasi-separated. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [AlgebraicGeometry.IsAffine Z.left]
      (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj Z ⟶ Y)
      (pZ : P ⟶ yoneda.obj Z) (pX : P ⟶ X),
      IsPullback pZ pX g f → QuasiSeparated pZ := by
  constructor
  · intro h Z hZ P g pZ pX sq
    exact h sq
  · intro h Z hZ P g pZ pX sq
    exact h Z P g pZ pX sq

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses
`forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X},
    IsPullback pZ pX g f → QuasiSeparated pZ) : forallAffine f := by
  exact h

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is quasi-separated. -/
theorem spec (h : forallAffine f) {Z : Over S}
    [AlgebraicGeometry.IsAffine Z.left] {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    (sq : IsPullback pZ pX g f) : QuasiSeparated pZ := by
  exact h sq

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme is quasi-separated whenever `forallAffine f` holds. -/
theorem pullback_snd {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    (h : forallAffine f) (g : yoneda.obj Z ⟶ Y) [HasPullback f g] :
    QuasiSeparated (pullback.snd f g) := by
  exact h (IsPullback.of_hasPullback f g).flip

end forallAffine

/-- Every affine-scheme-valued fibre product of `f` is a quasi-separated formal
algebraic space: every reduction is an absolutely quasi-separated algebraic space. -/
def forallAffineSpace : Prop :=
  ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    [IsFormalAlgebraicSpace P] (R : ReductionData P),
    IsPullback pZ pX g f →
      AlgebraicSpace.IsAbsolutelyQuasiSeparated R.space

/-- `forallAffineSpace f` means every affine-scheme-valued fibre product of `f`
has absolutely quasi-separated reduction. -/
theorem forallAffineSpace_iff : forallAffineSpace f ↔
    ∀ (Z : Over S) [AlgebraicGeometry.IsAffine Z.left]
      (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj Z ⟶ Y)
      (pZ : P ⟶ yoneda.obj Z) (pX : P ⟶ X)
      [IsFormalAlgebraicSpace P] (R : ReductionData P),
      IsPullback pZ pX g f →
        AlgebraicSpace.IsAbsolutelyQuasiSeparated R.space := by
  constructor
  · intro h Z hZ P g pZ pX hP R sq
    exact h R sq
  · intro h Z hZ P g pZ pX hP R sq
    exact h Z P g pZ pX R sq

namespace forallAffineSpace

/-- Affine-scheme-valued fibre products whose reductions are absolutely
quasi-separated witness `forallAffineSpace f`. -/
theorem of (h : ∀ {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    [IsFormalAlgebraicSpace P] (R : ReductionData P),
    IsPullback pZ pX g f →
      AlgebraicSpace.IsAbsolutelyQuasiSeparated R.space) :
    forallAffineSpace f := by
  exact h

/-- Under `forallAffineSpace f`, the reduction of any affine-scheme-valued
fibre product of `f` is absolutely quasi-separated. -/
theorem spec (h : forallAffineSpace f) {Z : Over S}
    [AlgebraicGeometry.IsAffine Z.left] {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    [IsFormalAlgebraicSpace P] (R : ReductionData P)
    (sq : IsPullback pZ pX g f) :
    AlgebraicSpace.IsAbsolutelyQuasiSeparated R.space := by
  exact h R sq

/-- The reduction of the chosen fibre product along a morphism from an affine
scheme is absolutely quasi-separated whenever `forallAffineSpace f` holds. -/
theorem pullback_snd {Z : Over S} [AlgebraicGeometry.IsAffine Z.left]
    (h : forallAffineSpace f) (g : yoneda.obj Z ⟶ Y) [HasPullback f g]
    [IsFormalAlgebraicSpace (pullback f g)] (R : ReductionData (pullback f g)) :
    AlgebraicSpace.IsAbsolutelyQuasiSeparated R.space := by
  exact h R (IsPullback.of_hasPullback f g).flip

end forallAffineSpace

/-- There is a jointly fppf-locally surjective étale covering of `Y` by affine
formal algebraic spaces, along which every pullback
of `f` is quasi-separated. -/
def existsCoverOnTarget : Prop :=
  ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
    (∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j)) ∧
      (∀ j, Etale (π j)) ∧
        Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (sigmaDesc π) ∧
          (∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
            IsPullback pY pX (π j) f → QuasiSeparated pY)

/-- `existsCoverOnTarget f` is the existence of an affine formal étale atlas of
`Y` along which pullbacks of `f` are quasi-separated. -/
theorem existsCoverOnTarget_iff : existsCoverOnTarget f ↔
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
      (∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j)) ∧
        (∀ j, Etale (π j)) ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
            (sigmaDesc π) ∧
            (∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
              IsPullback pY pX (π j) f → QuasiSeparated pY) := Iff.rfl

namespace existsCoverOnTarget

/-- An affine formal étale atlas of `Y` with quasi-separated pullbacks of `f`
witnesses `existsCoverOnTarget f`. -/
theorem of {ι : Type u} {Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    (π : (j : ι) → Y_ j ⟶ Y)
    (hAffine : ∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
      (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j))
    (hEtale : ∀ j, Etale (π j))
    (hCover : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (sigmaDesc π))
    (hQS : ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
      IsPullback pY pX (π j) f → QuasiSeparated pY) :
    existsCoverOnTarget f := by
  exact ⟨ι, Y_, π, hAffine, hEtale, hCover, hQS⟩

/-- `existsCoverOnTarget f` supplies an affine formal étale atlas of `Y` along
which pullbacks of `f` are quasi-separated. -/
theorem spec (h : existsCoverOnTarget f) :
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : (j : ι) → Y_ j ⟶ Y),
      (∀ j, ∃ (Λ : Type u) (_ : Preorder Λ) (_ : IsDirected Λ (· ≤ ·))
        (D : Λ ⥤ Over S), IsDirectedAffineThickeningColimit D (Y_ j)) ∧
        (∀ j, Etale (π j)) ∧
          Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
            (sigmaDesc π) ∧
            (∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
              IsPullback pY pX (π j) f → QuasiSeparated pY) := by
  exact h

end existsCoverOnTarget

end QuasiSeparated

namespace Separated

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y)

/-- For a morphism of formal algebraic spaces, separatedness
is equivalent to all scheme base changes having the property, all affine base
changes having it, all affine pullbacks having absolutely separated reductions
and the existence of an affine formal étale target atlas with the property. -/
theorem tfae [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Y) :
    List.TFAE [Separated f, forallScheme f, forallAffine f, forallAffineSpace f,
      existsCoverOnTarget f] := sorry

/-- A morphism of formal algebraic spaces is separated iff every scheme-valued
base change has separated projection. -/
theorem iff_forallScheme [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Y) : Separated f ↔ forallScheme f := by
  exact (tfae f).out 0 1

/-- A morphism of formal algebraic spaces is separated iff every
affine-scheme-valued base change has separated projection. -/
theorem iff_forallAffine [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Y) : Separated f ↔ forallAffine f := by
  exact (tfae f).out 0 2

/-- A morphism of formal algebraic spaces is separated iff every
affine-scheme-valued fibre product is a separated formal algebraic space. -/
theorem iff_forallAffineSpace [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Y) : Separated f ↔ forallAffineSpace f := by
  exact (tfae f).out 0 3

/-- A morphism of formal algebraic spaces is separated iff some affine formal étale
covering of the target has separated pullbacks of `f`. -/
theorem iff_existsCoverOnTarget [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Y) : Separated f ↔ existsCoverOnTarget f := by
  exact (tfae f).out 0 4

end Separated

namespace QuasiSeparated

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y)

/-- For a morphism of formal algebraic spaces, quasi-separatedness
is equivalent to all scheme base changes having the property, all affine base
changes having it, all affine pullbacks having absolutely quasi-separated
reductions, and the existence of an affine formal étale target atlas with the
property. -/
theorem tfae [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Y) :
    List.TFAE [QuasiSeparated f, forallScheme f, forallAffine f,
      forallAffineSpace f, existsCoverOnTarget f] := sorry

/-- A morphism of formal algebraic spaces is quasi-separated iff every
scheme-valued base change has quasi-separated projection. -/
theorem iff_forallScheme [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Y) : QuasiSeparated f ↔ forallScheme f := by
  exact (tfae f).out 0 1

/-- A morphism of formal algebraic spaces is quasi-separated iff every
affine-scheme-valued base change has quasi-separated projection. -/
theorem iff_forallAffine [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Y) : QuasiSeparated f ↔ forallAffine f := by
  exact (tfae f).out 0 2

/-- A morphism of formal algebraic spaces is quasi-separated iff every
affine-scheme-valued fibre product is a quasi-separated formal algebraic
space. -/
theorem iff_forallAffineSpace [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Y) :
    QuasiSeparated f ↔ forallAffineSpace f := by
  exact (tfae f).out 0 3

/-- A morphism of formal algebraic spaces is quasi-separated iff some
affine formal étale covering of the target has quasi-separated pullbacks of
`f`. -/
theorem iff_existsCoverOnTarget [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (f : X ⟶ Y) :
    QuasiSeparated f ↔ existsCoverOnTarget f := by
  exact (tfae f).out 0 4

end QuasiSeparated

end AlgebraicGeometry.FormalAlgebraicSpace
