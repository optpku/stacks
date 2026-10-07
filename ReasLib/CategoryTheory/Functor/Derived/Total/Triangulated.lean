module

public import ReasLib.CategoryTheory.Functor.Derived.DefinedAt.Triangulated
public import ReasLib.CategoryTheory.Functor.Derived.Definedness.Shift.Left
public import ReasLib.CategoryTheory.Functor.Derived.Definedness.Shift.Right
public import ReasLib.CategoryTheory.Functor.Derived.PointwiseValue.Total
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import Mathlib.CategoryTheory.Localization.Triangulated
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Triangulated Total Derived Functors

When a triangulated functor has a source-defined derived value at every object, its pointwise
values assemble into the canonical total derived functor. This leaf equips that total functor
with the shift and distinguished-triangle API expected by triangulated applications.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Functor

open Limits MorphismProperty Pretriangulated

variable {D : Type u₁} {D' : Type u₂} {E : Type u₃}
  [Category.{v₁} D] [Category.{v₂} D'] [Category.{v₃} E]
  (F : D ⥤ D') (S : MorphismProperty D) (L : D ⥤ E)

section Right

variable [HasShift D ℤ] [HasShift D' ℤ] [HasShift E ℤ]

/-- The extension unit exhibiting the source-shifted total right-derived functor as the
right-derived model of `shiftFunctor D n ⋙ F`. -/
@[stacks 05SE "total right-derived source-shift unit"]
noncomputable def totalRightDerivedShiftUnit (n : ℤ)
    [L.IsLocalization S] [L.CommShift ℤ]
    [F.HasPointwiseRightDerivedFunctor S] :
    shiftFunctor D n ⋙ F ⟶
      L ⋙ (shiftFunctor E n ⋙ F.totalRightDerived L S) :=
  (whiskerLeft (shiftFunctor D n) (F.totalRightDerivedUnit L S) ≫
    (associator _ _ _).inv) ≫
    whiskerRight (L.commShiftIso n).hom (F.totalRightDerived L S) ≫
    (associator _ _ _).hom

/-- The canonical shift comparison on the total right-derived functor.  Its first factor is
the uniqueness isomorphism for the source-shifted pointwise Kan extension; its second factor
identifies postcomposition by a shift with the Kan extension of the shifted target functor. -/
@[stacks 05SE "total right-derived shift comparison"]
noncomputable def totalRightDerivedShiftIso (n : ℤ)
    [F.CommShift ℤ] [L.IsLocalization S] [L.CommShift ℤ]
    [F.HasPointwiseRightDerivedFunctor S] :
    shiftFunctor E n ⋙ F.totalRightDerived L S ≅
      F.totalRightDerived L S ⋙ shiftFunctor D' n :=
  (@leftKanExtensionUniqueOfIso _ _ _ _ _ _
      (shiftFunctor E n ⋙ F.totalRightDerived L S)
      (L := L) (F := shiftFunctor D n ⋙ F)
      (totalRightDerivedShiftUnit F S L n)
      (((isLeftKanExtension_iff_postcomp₁
          (shiftFunctor E n) (L.commShiftIso n).symm
          (whiskerLeft (shiftFunctor D n) (F.totalRightDerivedUnit L S) ≫
            (associator _ _ _).inv)).mp
        ((isLeftKanExtension_iff_precomp
          (F.totalRightDerived L S) (shiftFunctor D n)
          (F.totalRightDerivedUnit L S)).mp
            ((isRightDerivedFunctor_iff_isLeftKanExtension
              (RF := F.totalRightDerived L S)
              (α := F.totalRightDerivedUnit L S) S).mp inferInstance))))
      (G := F ⋙ shiftFunctor D' n) (F.commShiftIso n)
      (F.totalRightDerived L S ⋙ shiftFunctor D' n)
      (whiskerRight (F.totalRightDerivedUnit L S) (shiftFunctor D' n) ≫
        (associator _ _ _).hom)
      (LeftExtension.isPointwiseLeftKanExtensionEquivOfIso
        (LeftExtension.postcompose₂ObjMkIso (shiftFunctor D' n)
          (F.totalRightDerivedUnit L S))
        ((isPointwiseLeftKanExtensionOfHasPointwiseRightDerivedFunctor
          (F' := F.totalRightDerived L S) (F := F) (L := L)
          (α := F.totalRightDerivedUnit L S) (W := S)).postcompose
            (shiftFunctor D' n))).isLeftKanExtension)

/-- The canonical total right-derived shift comparison agrees with the zero-shift
comparison. -/
@[stacks 05SE "total right-derived zero-shift coherence"]
theorem totalRightDerivedShiftIso_zero
    [F.CommShift ℤ] [L.IsLocalization S] [L.CommShift ℤ]
    [F.HasPointwiseRightDerivedFunctor S] :
    totalRightDerivedShiftIso F S L 0 =
      Functor.CommShift.isoZero (F.totalRightDerived L S) ℤ := sorry

/-- The canonical total right-derived shift comparison is coherent with addition of
integer shifts. -/
@[stacks 05SE "total right-derived additive-shift coherence"]
theorem totalRightDerivedShiftIso_add
    [F.CommShift ℤ] [L.IsLocalization S] [L.CommShift ℤ]
    [F.HasPointwiseRightDerivedFunctor S] (a b : ℤ) :
    totalRightDerivedShiftIso F S L (a + b) =
      Functor.CommShift.isoAdd (totalRightDerivedShiftIso F S L a)
        (totalRightDerivedShiftIso F S L b) := sorry

/-- Relative to any shift-compatible localization model, a pointwise
total right-derived functor commutes with integer shifts. -/
@[stacks 05SE "total right-derived shift"]
noncomputable instance totalRightDerived_commShift
    [F.CommShift ℤ] [L.IsLocalization S] [L.CommShift ℤ]
    [F.HasPointwiseRightDerivedFunctor S] :
    (F.totalRightDerived L S).CommShift ℤ where
  commShiftIso n := totalRightDerivedShiftIso F S L n
  commShiftIso_zero := totalRightDerivedShiftIso_zero F S L
  commShiftIso_add := totalRightDerivedShiftIso_add F S L

/-- Relative to any triangulated localization model, an everywhere
source-defined total right-derived functor is triangulated. -/
@[stacks 05SE "total right-derived exactness", stacks 09LK]
instance totalRightDerived_isTriangulated
    [HasZeroObject D] [HasZeroObject D'] [HasZeroObject E]
    [Preadditive D] [Preadditive D'] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [∀ n : ℤ, (shiftFunctor E n).Additive]
    [Pretriangulated D] [Pretriangulated D'] [Pretriangulated E]
    [_root_.CategoryTheory.IsTriangulated D]
    [_root_.CategoryTheory.IsTriangulated D']
    [_root_.CategoryTheory.IsTriangulated E]
    [F.CommShift ℤ] [F.IsTriangulated]
    [L.IsLocalization S] [L.CommShift ℤ] [L.IsTriangulated]
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]
    [Functor.RightDerived.EverywhereDefined F S] :
    (F.totalRightDerived L S).IsTriangulated := sorry

end Right

section Left

variable [HasShift D ℤ] [HasShift D' ℤ] [HasShift E ℤ]

/-- The extension counit exhibiting the source-shifted total left-derived functor as the
left-derived model of `shiftFunctor D n ⋙ F`. -/
@[stacks 05SE "total left-derived source-shift counit"]
noncomputable def totalLeftDerivedShiftCounit (n : ℤ)
    [L.IsLocalization S] [L.CommShift ℤ]
    [F.HasPointwiseLeftDerivedFunctor S] :
    L ⋙ (shiftFunctor E n ⋙ F.totalLeftDerived L S) ⟶
      shiftFunctor D n ⋙ F :=
  (associator _ _ _).inv ≫
    whiskerRight (L.commShiftIso n).inv (F.totalLeftDerived L S) ≫
    ((associator _ _ _).hom ≫
      whiskerLeft (shiftFunctor D n) (F.totalLeftDerivedCounit L S))

/-- The canonical shift comparison on the total left-derived functor.  It compares the
source-shifted pointwise Kan extension with the target-shifted one through
`F.commShiftIso`. -/
@[stacks 05SE "total left-derived shift comparison"]
noncomputable def totalLeftDerivedShiftIso (n : ℤ)
    [F.CommShift ℤ] [L.IsLocalization S] [L.CommShift ℤ]
    [F.HasPointwiseLeftDerivedFunctor S] :
    shiftFunctor E n ⋙ F.totalLeftDerived L S ≅
      F.totalLeftDerived L S ⋙ shiftFunctor D' n :=
  @rightKanExtensionUniqueOfIso _ _ _ _ _ _
      (shiftFunctor E n ⋙ F.totalLeftDerived L S)
      (L := L) (F := shiftFunctor D n ⋙ F)
      (totalLeftDerivedShiftCounit F S L n)
      (((isRightKanExtension_iff_postcomp₁
          (shiftFunctor E n) (L.commShiftIso n).symm
          ((associator _ _ _).hom ≫
            whiskerLeft (shiftFunctor D n) (F.totalLeftDerivedCounit L S))).mp
        ((isRightKanExtension_iff_precomp
          (F.totalLeftDerived L S) (shiftFunctor D n)
          (F.totalLeftDerivedCounit L S)).mp
            ((isLeftDerivedFunctor_iff_isRightKanExtension
              (LF := F.totalLeftDerived L S)
              (α := F.totalLeftDerivedCounit L S) S).mp inferInstance))))
      (G := F ⋙ shiftFunctor D' n) (F.commShiftIso n)
      (F.totalLeftDerived L S ⋙ shiftFunctor D' n)
      ((associator _ _ _).inv ≫
        whiskerRight (F.totalLeftDerivedCounit L S) (shiftFunctor D' n))
      (RightExtension.isPointwiseRightKanExtensionEquivOfIso
        (RightExtension.postcompose₂ObjMkIso (shiftFunctor D' n)
          (F.totalLeftDerivedCounit L S))
        ((isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor
          (F' := F.totalLeftDerived L S) (F := F) (L := L)
          (α := F.totalLeftDerivedCounit L S) (W := S)).postcompose
            (shiftFunctor D' n))).isRightKanExtension

/-- The canonical total left-derived shift comparison agrees with the zero-shift
comparison. -/
@[stacks 05SE "total left-derived zero-shift coherence"]
theorem totalLeftDerivedShiftIso_zero
    [F.CommShift ℤ] [L.IsLocalization S] [L.CommShift ℤ]
    [F.HasPointwiseLeftDerivedFunctor S] :
    totalLeftDerivedShiftIso F S L 0 =
      Functor.CommShift.isoZero (F.totalLeftDerived L S) ℤ := sorry

/-- The canonical total left-derived shift comparison is coherent with addition of integer
shifts. -/
@[stacks 05SE "total left-derived additive-shift coherence"]
theorem totalLeftDerivedShiftIso_add
    [F.CommShift ℤ] [L.IsLocalization S] [L.CommShift ℤ]
    [F.HasPointwiseLeftDerivedFunctor S] (a b : ℤ) :
    totalLeftDerivedShiftIso F S L (a + b) =
      Functor.CommShift.isoAdd (totalLeftDerivedShiftIso F S L a)
        (totalLeftDerivedShiftIso F S L b) := sorry

/-- Relative to any shift-compatible localization model, a pointwise
total left-derived functor commutes with integer shifts. -/
@[stacks 05SE "total left-derived shift"]
noncomputable instance totalLeftDerived_commShift
    [F.CommShift ℤ] [L.IsLocalization S] [L.CommShift ℤ]
    [F.HasPointwiseLeftDerivedFunctor S] :
    (F.totalLeftDerived L S).CommShift ℤ where
  commShiftIso n := totalLeftDerivedShiftIso F S L n
  commShiftIso_zero := totalLeftDerivedShiftIso_zero F S L
  commShiftIso_add := totalLeftDerivedShiftIso_add F S L

/-- Relative to any triangulated localization model, an everywhere
source-defined total left-derived functor is triangulated. -/
@[stacks 05SE "total left-derived exactness"]
instance totalLeftDerived_isTriangulated
    [HasZeroObject D] [HasZeroObject D'] [HasZeroObject E]
    [Preadditive D] [Preadditive D'] [Preadditive E]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [∀ n : ℤ, (shiftFunctor D' n).Additive]
    [∀ n : ℤ, (shiftFunctor E n).Additive]
    [Pretriangulated D] [Pretriangulated D'] [Pretriangulated E]
    [_root_.CategoryTheory.IsTriangulated D]
    [_root_.CategoryTheory.IsTriangulated D']
    [_root_.CategoryTheory.IsTriangulated E]
    [F.CommShift ℤ] [F.IsTriangulated]
    [L.IsLocalization S] [L.CommShift ℤ] [L.IsTriangulated]
    [IsSaturatedMultiplicativeSystem S] [S.IsCompatibleWithTriangulation]
    [Functor.LeftDerived.EverywhereDefined F S] :
    (F.totalLeftDerived L S).IsTriangulated := sorry

end Left



end CategoryTheory.Functor
