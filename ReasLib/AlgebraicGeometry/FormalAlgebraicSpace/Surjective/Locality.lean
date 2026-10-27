/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.EtaleCover
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Data.List.TFAE

/-!
# Local tests for surjective morphisms of formal algebraic spaces

Surjectivity on reductions can be tested after scheme or affine scheme base
change, on an affine étale target covering, or along a surjective morphism
of formal algebraic spaces to the target.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.Surjective

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)

/-- The projection of every scheme-valued base change of `f` is surjective. -/
def forallScheme : Prop :=
  ∀ {Z : Over S} {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    [hP : IsFormalAlgebraicSpace P] (RZ : ReductionData (yoneda.obj Z)) (RP : ReductionData P),
    IsPullback pZ pX g f → ReductionData.Surjective RP RZ pZ

/-- `forallScheme f` means every scheme-valued pullback projection of `f` is
surjective. -/
theorem forallScheme_iff : forallScheme f ↔
    ∀ (Z : Over S) (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj Z ⟶ Y)
      (pZ : P ⟶ yoneda.obj Z) (pX : P ⟶ X)
      [hP : IsFormalAlgebraicSpace P] (RZ : ReductionData (yoneda.obj Z)) (RP : ReductionData P),
      IsPullback pZ pX g f → ReductionData.Surjective RP RZ pZ := sorry

namespace forallScheme

/-- A universal scheme-valued pullback condition witnesses `forallScheme f`. -/
theorem of (h : ∀ {Z : Over S} {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    [hP : IsFormalAlgebraicSpace P] (RZ : ReductionData (yoneda.obj Z)) (RP : ReductionData P),
    IsPullback pZ pX g f → ReductionData.Surjective RP RZ pZ) : forallScheme f := sorry

/-- Under `forallScheme f`, the test-leg of any scheme-valued pullback of `f` is
surjective. -/
theorem spec (h : forallScheme f) {Z : Over S} {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    [hP : IsFormalAlgebraicSpace P] (RZ : ReductionData (yoneda.obj Z)) (RP : ReductionData P)
    (sq : IsPullback pZ pX g f) : ReductionData.Surjective RP RZ pZ := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from a
scheme is surjective whenever `forallScheme f` holds. -/
theorem pullback_snd {Z : Over S} (RZ : ReductionData (yoneda.obj Z))
    (h : forallScheme f) (g : yoneda.obj Z ⟶ Y) [HasPullback f g]
    [hP : IsFormalAlgebraicSpace (pullback f g)] (RP : ReductionData (pullback f g)) :
    ReductionData.Surjective RP RZ (pullback.snd f g) := sorry

end forallScheme

/-- The projection of every affine-scheme-valued base change of `f` is
surjective. -/
def forallAffine : Prop :=
  ∀ {Z : Over S} [hZ : AlgebraicGeometry.IsAffine Z.left]
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    [hP : IsFormalAlgebraicSpace P] (RZ : ReductionData (yoneda.obj Z)) (RP : ReductionData P),
    IsPullback pZ pX g f → ReductionData.Surjective RP RZ pZ

/-- `forallAffine f` means every affine-scheme-valued pullback projection of `f`
is surjective. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (Z : Over S) [hZ : AlgebraicGeometry.IsAffine Z.left]
      (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj Z ⟶ Y)
      (pZ : P ⟶ yoneda.obj Z) (pX : P ⟶ X)
      [hP : IsFormalAlgebraicSpace P] (RZ : ReductionData (yoneda.obj Z)) (RP : ReductionData P),
      IsPullback pZ pX g f → ReductionData.Surjective RP RZ pZ := sorry

namespace forallAffine

/-- A universal affine-scheme-valued pullback condition witnesses
`forallAffine f`. -/
theorem of (h : ∀ {Z : Over S} [hZ : AlgebraicGeometry.IsAffine Z.left]
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj Z ⟶ Y}
    {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    [hP : IsFormalAlgebraicSpace P] (RZ : ReductionData (yoneda.obj Z)) (RP : ReductionData P),
    IsPullback pZ pX g f → ReductionData.Surjective RP RZ pZ) : forallAffine f := sorry

/-- Under `forallAffine f`, the test-leg of any affine-scheme-valued pullback of
`f` is surjective. -/
theorem spec (h : forallAffine f) {Z : Over S}
    [hZ : AlgebraicGeometry.IsAffine Z.left] {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj Z ⟶ Y} {pZ : P ⟶ yoneda.obj Z} {pX : P ⟶ X}
    [hP : IsFormalAlgebraicSpace P] (RZ : ReductionData (yoneda.obj Z)) (RP : ReductionData P)
    (sq : IsPullback pZ pX g f) : ReductionData.Surjective RP RZ pZ := sorry

/-- The chosen pullback projection `pullback.snd f g` along a morphism from an
affine scheme is surjective whenever `forallAffine f` holds. -/
theorem pullback_snd {Z : Over S} [hZ : AlgebraicGeometry.IsAffine Z.left]
    (RZ : ReductionData (yoneda.obj Z)) (h : forallAffine f) (g : yoneda.obj Z ⟶ Y)
    [HasPullback f g] [hP : IsFormalAlgebraicSpace (pullback f g)]
    (RP : ReductionData (pullback f g)) : ReductionData.Surjective RP RZ (pullback.snd f g) := sorry

end forallAffine

/-- Some affine étale covering of the target has surjective pullback
projections on every pair of reductions. -/
def existsCoverOnTarget : Prop :=
  ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ j, Y_ j ⟶ Y),
    IsEtaleAffineCover π ∧
      ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X}
        [hY : IsFormalAlgebraicSpace (Y_ j)] [hP : IsFormalAlgebraicSpace P]
        (RYj : ReductionData (Y_ j)) (RP : ReductionData P),
        IsPullback pY pX (π j) f → ReductionData.Surjective RP RYj pY

/-- The target-cover test is equivalent to existence of an affine étale
covering with surjective pullback projections. -/
theorem existsCoverOnTarget_iff : existsCoverOnTarget f ↔
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ j, Y_ j ⟶ Y),
      IsEtaleAffineCover π ∧
        ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X}
          [hY : IsFormalAlgebraicSpace (Y_ j)] [hP : IsFormalAlgebraicSpace P]
          (RYj : ReductionData (Y_ j)) (RP : ReductionData P),
          IsPullback pY pX (π j) f → ReductionData.Surjective RP RYj pY := sorry

namespace existsCoverOnTarget

/-- An affine étale target covering with surjective pullback projections
implies the target-cover test. -/
theorem of {ι : Type u} {Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    (π : ∀ j, Y_ j ⟶ Y) (hCover : IsEtaleAffineCover π)
    (hSurj : ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X}
      [hY : IsFormalAlgebraicSpace (Y_ j)] [hP : IsFormalAlgebraicSpace P]
      (RYj : ReductionData (Y_ j)) (RP : ReductionData P),
      IsPullback pY pX (π j) f → ReductionData.Surjective RP RYj pY) :
    existsCoverOnTarget f := sorry

/-- The target-cover test supplies an affine étale covering and
surjectivity of all its pullback projections. -/
theorem spec (h : existsCoverOnTarget f) :
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ j, Y_ j ⟶ Y),
      IsEtaleAffineCover π ∧
        ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X}
          [hY : IsFormalAlgebraicSpace (Y_ j)] [hP : IsFormalAlgebraicSpace P]
          (RYj : ReductionData (Y_ j)) (RP : ReductionData P),
          IsPullback pY pX (π j) f → ReductionData.Surjective RP RYj pY := sorry

end existsCoverOnTarget

section SurjectiveTarget

variable [hY : IsFormalAlgebraicSpace Y] (RY : ReductionData Y)

/-- Some surjective morphism of formal algebraic spaces to the target
has surjective pullback projections on all reductions. -/
def existsSurjectiveOnTarget (RY : ReductionData Y) (f : X ⟶ Y) : Prop :=
  ∃ (Z : (Over S)ᵒᵖ ⥤ Type u) (hZ : IsFormalAlgebraicSpace Z)
    (RZ : ReductionData Z) (g : Z ⟶ Y),
    ReductionData.Surjective RZ RY g ∧
      ∀ {P : (Over S)ᵒᵖ ⥤ Type u} {pZ : P ⟶ Z} {pX : P ⟶ X}
        [hP : IsFormalAlgebraicSpace P] (RP : ReductionData P),
        IsPullback pZ pX g f → ReductionData.Surjective RP RZ pZ

/-- The surjective-target test is equivalent to existence of a surjective
formal-space morphism with surjective pullback projections. -/
theorem existsSurjectiveOnTarget_iff : existsSurjectiveOnTarget RY f ↔
    ∃ (Z : (Over S)ᵒᵖ ⥤ Type u) (hZ : IsFormalAlgebraicSpace Z)
      (RZ : ReductionData Z) (g : Z ⟶ Y),
      ReductionData.Surjective RZ RY g ∧
        ∀ {P : (Over S)ᵒᵖ ⥤ Type u} {pZ : P ⟶ Z} {pX : P ⟶ X}
          [hP : IsFormalAlgebraicSpace P] (RP : ReductionData P),
          IsPullback pZ pX g f → ReductionData.Surjective RP RZ pZ := sorry

namespace existsSurjectiveOnTarget

/-- A surjective morphism to the target with surjective pullback projections
implies the surjective-target test. -/
theorem of {Z : (Over S)ᵒᵖ ⥤ Type u} [hZ : IsFormalAlgebraicSpace Z]
    (RZ : ReductionData Z) (g : Z ⟶ Y) (hg : ReductionData.Surjective RZ RY g)
    (h : ∀ {P : (Over S)ᵒᵖ ⥤ Type u} {pZ : P ⟶ Z} {pX : P ⟶ X}
      [hP : IsFormalAlgebraicSpace P] (RP : ReductionData P),
      IsPullback pZ pX g f → ReductionData.Surjective RP RZ pZ) :
    existsSurjectiveOnTarget RY f := sorry

/-- The surjective-target test supplies a surjective formal-space morphism
and surjectivity of all its pullback projections. -/
theorem spec (h : existsSurjectiveOnTarget RY f) :
    ∃ (Z : (Over S)ᵒᵖ ⥤ Type u) (hZ : IsFormalAlgebraicSpace Z)
      (RZ : ReductionData Z) (g : Z ⟶ Y),
      ReductionData.Surjective RZ RY g ∧
        ∀ {P : (Over S)ᵒᵖ ⥤ Type u} {pZ : P ⟶ Z} {pX : P ⟶ X}
          [hP : IsFormalAlgebraicSpace P] (RP : ReductionData P),
          IsPullback pZ pX g f → ReductionData.Surjective RP RZ pZ := sorry

end existsSurjectiveOnTarget

end SurjectiveTarget

/-- Surjectivity on reductions is equivalent to the scheme test, the affine
scheme test, the affine étale target-cover test, and the surjective-target test. -/
theorem tfae [hX : IsFormalAlgebraicSpace X] [hY : IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) :
    List.TFAE [ReductionData.Surjective RX RY f, forallScheme f, forallAffine f,
      existsCoverOnTarget f, existsSurjectiveOnTarget RY f] := sorry

/-- Surjectivity on reductions is equivalent to surjectivity of every
scheme-valued base-change projection. -/
theorem iff_forallScheme [hX : IsFormalAlgebraicSpace X] [hY : IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) :
    ReductionData.Surjective RX RY f ↔ forallScheme f := sorry

/-- Surjectivity on reductions is equivalent to surjectivity of every
affine-scheme-valued base-change projection. -/
theorem iff_forallAffine [hX : IsFormalAlgebraicSpace X] [hY : IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) :
    ReductionData.Surjective RX RY f ↔ forallAffine f := sorry

/-- Surjectivity on reductions is equivalent to existence of an affine étale
target covering with surjective pullback projections. -/
theorem iff_existsCoverOnTarget
    [hX : IsFormalAlgebraicSpace X] [hY : IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) :
    ReductionData.Surjective RX RY f ↔ existsCoverOnTarget f := sorry

/-- Surjectivity on reductions is equivalent to existence of a surjective
formal-space morphism to the target with surjective pullback projections. -/
theorem iff_existsSurjectiveOnTarget
    [hX : IsFormalAlgebraicSpace X] [hY : IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) :
    ReductionData.Surjective RX RY f ↔ existsSurjectiveOnTarget RY f := sorry

end AlgebraicGeometry.FormalAlgebraicSpace.Surjective
