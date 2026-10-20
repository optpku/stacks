/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Pretriangulated.Functor.TriangulatedStructure

@[expose] public section

/-!
# Homological and Triangulated Localization Lifts

This leaf packages the structures carried by the canonical lift of a functor
through an arbitrary localization.  It is intentionally formulated for a
localization functor `L`, rather than only for a chosen quotient construction:
the same API applies to Verdier quotients, derived-category localizations, and
other exact localizations.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.Localization

open Limits MorphismProperty Pretriangulated

section CommShift

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]

/-- the canonical lift of a shift-commuting functor through a
shift-commuting localization functor also commutes with shifts. -/
@[stacks 05R7]
noncomputable instance liftCommShift
    (W : MorphismProperty C) (L : C ⥤ D) [L.IsLocalization W]
    [L.CommShift ℤ] (F : C ⥤ E) [F.CommShift ℤ] (hF : W.IsInvertedBy F) :
    (lift F hF L).CommShift ℤ :=
  Functor.commShiftOfLocalization L W ℤ F (lift F hF L)

/-- The canonical factorization of a shift-commuting functor through a shift-commuting
localization commutes with shifts. -/
@[stacks 05R7]
noncomputable instance facCommShift
    (W : MorphismProperty C) (L : C ⥤ D) [L.IsLocalization W]
    [L.CommShift ℤ] (F : C ⥤ E) [F.CommShift ℤ] (hF : W.IsInvertedBy F) :
    NatTrans.CommShift (fac F hF L).hom ℤ := sorry

end CommShift

section Homological

variable {C : Type u₁} {D : Type u₂} {A : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} A]
  [HasZeroObject C] [HasZeroObject D] [HasShift C ℤ] [HasShift D ℤ]
  [Preadditive C] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D] [Abelian A]

/-- a homological functor remains homological after its canonical
factorization through a triangulated localization. -/
@[stacks 05R7]
theorem lift_isHomological
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
    (L : C ⥤ D) [L.IsLocalization W] [L.CommShift ℤ] [L.IsTriangulated]
    (H : C ⥤ A) [H.IsHomological] (hH : W.IsInvertedBy H) :
    (lift H hH L).IsHomological := sorry

/-- homologicality descends to any strict factorization through a
triangulated localization functor. -/
@[stacks 05R7]
theorem isHomological_of_comp_eq
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
    (L : C ⥤ D) [L.IsLocalization W] [L.CommShift ℤ] [L.IsTriangulated]
    (H : C ⥤ A) [H.IsHomological] (H' : D ⥤ A) (hfac : L ⋙ H' = H) :
    H'.IsHomological := sorry

end Homological

section Triangulated

variable {C : Type u₁} {D : Type u₂} {E : Type u₃}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E]
  [HasZeroObject C] [HasZeroObject D] [HasZeroObject E]
  [HasShift C ℤ] [HasShift D ℤ] [HasShift E ℤ]
  [Preadditive C] [Preadditive D] [Preadditive E]
  [∀ n : ℤ, (shiftFunctor C n).Additive]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor E n).Additive]
  [Pretriangulated C] [Pretriangulated D] [Pretriangulated E]

/-- an exact functor remains exact after its canonical
factorization through a triangulated localization. -/
@[stacks 05R7]
theorem lift_isTriangulated
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
    (L : C ⥤ D) [L.IsLocalization W] [L.CommShift ℤ] [L.IsTriangulated]
    (F : C ⥤ E) [F.CommShift ℤ] [F.IsTriangulated] (hF : W.IsInvertedBy F) :
    (lift F hF L).IsTriangulated := sorry

/-- any strict factorization of an exact functor through a
triangulated localization admits a canonical-compatible triangulated structure. -/
@[stacks 05R7]
theorem hasTriangulatedStructure_of_comp_eq
    (W : MorphismProperty C) [W.HasLeftCalculusOfFractions]
    (L : C ⥤ D) [L.IsLocalization W] [L.CommShift ℤ] [L.IsTriangulated]
    (F : C ⥤ E) [F.CommShift ℤ] [F.IsTriangulated]
    (F' : D ⥤ E) (hfac : L ⋙ F' = F) :
    F'.HasTriangulatedStructure := sorry

end Triangulated


end CategoryTheory.Localization
