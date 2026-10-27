/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalAlgebraicSpace.QuasiCompact
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import Mathlib.Data.List.TFAE

/-!
# Local tests for quasi-compact morphisms of formal algebraic spaces

Quasi-compactness of the induced map on reductions can be tested on pullbacks
along quasi-compact schemes, affine schemes, or an affine étale target covering.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.FormalAlgebraicSpace.QuasiCompact

variable {S : Scheme.{u}} {X Y : (Over S)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)

/-- Every fibre product along a morphism from a quasi-compact scheme is a
quasi-compact formal algebraic space. -/
def forallQuasiCompactScheme : Prop :=
  ∀ {T : Over S} {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj T ⟶ Y}
    {pT : P ⟶ yoneda.obj T} {pX : P ⟶ X} [CompactSpace T.left],
    IsPullback pT pX g f → IsQuasiCompact P

/-- The quasi-compact scheme test is equivalent to quasi-compactness of every
cartesian-square vertex over a quasi-compact scheme. -/
theorem forallQuasiCompactScheme_iff : forallQuasiCompactScheme f ↔
    ∀ (T : Over S) (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj T ⟶ Y)
      (pT : P ⟶ yoneda.obj T) (pX : P ⟶ X) [CompactSpace T.left],
      IsPullback pT pX g f → IsQuasiCompact P := by
  constructor
  · intro h T P g pT pX _ sq
    exact h sq
  · intro h T P g pT pX _ sq
    exact h T P g pT pX sq

namespace forallQuasiCompactScheme

/-- The universal quasi-compact scheme pullback condition implies the
quasi-compact scheme test. -/
theorem of
    (h : ∀ {T : Over S} {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj T ⟶ Y}
      {pT : P ⟶ yoneda.obj T} {pX : P ⟶ X} [CompactSpace T.left],
      IsPullback pT pX g f → IsQuasiCompact P) :
    forallQuasiCompactScheme f := h

/-- The quasi-compact scheme test makes every cartesian-square vertex over a
quasi-compact scheme a quasi-compact formal algebraic space. -/
theorem spec (h : forallQuasiCompactScheme f) {T : Over S}
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj T ⟶ Y}
    {pT : P ⟶ yoneda.obj T} {pX : P ⟶ X} [CompactSpace T.left]
    (sq : IsPullback pT pX g f) : IsQuasiCompact P :=
  h sq

/-- The chosen pullback along a quasi-compact scheme is quasi-compact when
the quasi-compact scheme test holds. -/
theorem pullback_snd {T : Over S} [CompactSpace T.left]
    (h : forallQuasiCompactScheme f) (g : yoneda.obj T ⟶ Y) [HasPullback f g] :
    IsQuasiCompact (pullback f g) :=
  h (IsPullback.of_hasPullback f g).flip

end forallQuasiCompactScheme

/-- Every fibre product along a morphism from an affine scheme is a
quasi-compact formal algebraic space. -/
def forallAffine : Prop :=
  ∀ {T : Over S} [AlgebraicGeometry.IsAffine T.left]
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj T ⟶ Y}
    {pT : P ⟶ yoneda.obj T} {pX : P ⟶ X},
    IsPullback pT pX g f → IsQuasiCompact P

/-- The affine scheme test is equivalent to quasi-compactness of every
cartesian-square vertex over an affine scheme. -/
theorem forallAffine_iff : forallAffine f ↔
    ∀ (T : Over S) [AlgebraicGeometry.IsAffine T.left]
      (P : (Over S)ᵒᵖ ⥤ Type u) (g : yoneda.obj T ⟶ Y)
      (pT : P ⟶ yoneda.obj T) (pX : P ⟶ X),
      IsPullback pT pX g f → IsQuasiCompact P := by
  constructor
  · intro h T _ P g pT pX sq
    exact h sq
  · intro h T _ P g pT pX sq
    exact h T P g pT pX sq

namespace forallAffine

/-- The universal affine scheme pullback condition implies the affine scheme test. -/
theorem of (h : ∀ {T : Over S} [AlgebraicGeometry.IsAffine T.left]
    {P : (Over S)ᵒᵖ ⥤ Type u} {g : yoneda.obj T ⟶ Y}
    {pT : P ⟶ yoneda.obj T} {pX : P ⟶ X},
    IsPullback pT pX g f → IsQuasiCompact P) : forallAffine f := h

/-- The affine scheme test makes every cartesian-square vertex over an affine
scheme a quasi-compact formal algebraic space. -/
theorem spec (h : forallAffine f) {T : Over S}
    [AlgebraicGeometry.IsAffine T.left] {P : (Over S)ᵒᵖ ⥤ Type u}
    {g : yoneda.obj T ⟶ Y} {pT : P ⟶ yoneda.obj T} {pX : P ⟶ X}
    (sq : IsPullback pT pX g f) : IsQuasiCompact P :=
  h sq

/-- The chosen pullback along an affine scheme is quasi-compact when the
affine scheme test holds. -/
theorem pullback_snd {T : Over S} [AlgebraicGeometry.IsAffine T.left]
    (h : forallAffine f) (g : yoneda.obj T ⟶ Y) [HasPullback f g] :
    IsQuasiCompact (pullback f g) :=
  h (IsPullback.of_hasPullback f g).flip

end forallAffine

/-- Some affine étale covering of the target has quasi-compact formal algebraic
spaces as all its pullback vertices. -/
def existsCoverOnTarget : Prop :=
  ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ j, Y_ j ⟶ Y),
    IsEtaleAffineCover π ∧
      ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
        IsPullback pY pX (π j) f → IsQuasiCompact P

/-- The target-cover test is equivalent to existence of an affine étale
covering whose every cartesian-square vertex is quasi-compact. -/
theorem existsCoverOnTarget_iff : existsCoverOnTarget f ↔
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ j, Y_ j ⟶ Y),
      IsEtaleAffineCover π ∧
        ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
          IsPullback pY pX (π j) f → IsQuasiCompact P := Iff.rfl

namespace existsCoverOnTarget

/-- An affine étale target covering with quasi-compact pullback vertices
implies the target-cover test. -/
theorem of {ι : Type u} {Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)}
    (π : ∀ j, Y_ j ⟶ Y) (hCover : IsEtaleAffineCover π)
    (hQC : ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
      IsPullback pY pX (π j) f → IsQuasiCompact P) :
    existsCoverOnTarget f :=
  ⟨ι, Y_, π, hCover, hQC⟩

/-- The target-cover test supplies an affine étale covering and
quasi-compactness of all its pullback vertices. -/
theorem spec (h : existsCoverOnTarget f) :
    ∃ (ι : Type u) (Y_ : ι → ((Over S)ᵒᵖ ⥤ Type u)) (π : ∀ j, Y_ j ⟶ Y),
      IsEtaleAffineCover π ∧
        ∀ j {P : (Over S)ᵒᵖ ⥤ Type u} {pY : P ⟶ Y_ j} {pX : P ⟶ X},
          IsPullback pY pX (π j) f → IsQuasiCompact P := h

end existsCoverOnTarget

/-- Quasi-compactness of the induced map on reductions is equivalent to the
quasi-compact scheme test, the affine scheme test, and the target-cover test. -/
theorem tfae [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) :
    List.TFAE [ReductionData.QuasiCompact RX RY f,
      forallQuasiCompactScheme f, forallAffine f, existsCoverOnTarget f] := sorry

/-- The induced map on reductions is quasi-compact if and only if the
quasi-compact scheme test holds. -/
theorem iff_forallQuasiCompactScheme
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) :
    ReductionData.QuasiCompact RX RY f ↔ forallQuasiCompactScheme f :=
  (tfae RX RY f).out 0 1

/-- The induced map on reductions is quasi-compact if and only if the affine
scheme test holds. -/
theorem iff_forallAffine [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) :
    ReductionData.QuasiCompact RX RY f ↔ forallAffine f :=
  (tfae RX RY f).out 0 2

/-- The induced map on reductions is quasi-compact if and only if an affine
étale target covering has quasi-compact pullback vertices. -/
theorem iff_existsCoverOnTarget
    [IsFormalAlgebraicSpace X] [IsFormalAlgebraicSpace Y]
    (RX : ReductionData X) (RY : ReductionData Y) (f : X ⟶ Y) :
    ReductionData.QuasiCompact RX RY f ↔ existsCoverOnTarget f :=
  (tfae RX RY f).out 0 3

end AlgebraicGeometry.FormalAlgebraicSpace.QuasiCompact
