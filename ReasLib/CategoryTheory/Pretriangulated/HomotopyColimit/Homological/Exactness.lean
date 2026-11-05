/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Pretriangulated.HomotopyColimit.Homological.Image
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Triangulated.HomologicalFunctor
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Exactness Criterion for Images of Telescope Presentations

A homological functor takes a telescope presentation to a colimit cocone when
sequential colimits are exact and both the explicitly retained coproduct and
its shift by one remain colimiting after applying the functor.
-/

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v₁ u₁ v₂ u₂

noncomputable section

namespace CategoryTheory.HomotopyColimit.Presentation

variable {D : Type u₁} [Category.{v₁} D] [HasZeroObject D] [Preadditive D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable {A : Type u₂} [Category.{v₂} A]
variable {K : ℕ ⥤ D} {X : D}

namespace ImageCocone

/-- The image cocone is colimiting when the target has exact sequential colimits and both
the explicit coproduct cocone and its shift by one remain colimiting after applying the
homological functor. -/
@[stacks 0CRK]
theorem nonemptyIsColimit (P : Presentation K X) (H : D ⥤ A)
    [HasColimitsOfShape ℕ A] [IsTriangulated D] [Abelian A]
    [Functor.IsHomological H] [HasExactColimitsOfShape ℕ A]
    (h_coproduct : Nonempty (IsColimit (H.mapCocone P.coproduct.cocone)))
    (h_shifted_coproduct : Nonempty (IsColimit
      (H.mapCocone ((shiftFunctor D (1 : ℤ)).mapCocone P.coproduct.cocone)))) :
    Nonempty (IsColimit (imageCocone P H)) := sorry

/-- Preservation of the coproducts of the terms and their shifts supplies both hypotheses in
`ImageCocone.nonemptyIsColimit`. -/
theorem nonemptyIsColimitOfPreserves (P : Presentation K X) (H : D ⥤ A)
    [HasColimitsOfShape ℕ A] [IsTriangulated D] [Abelian A]
    [Functor.IsHomological H] [HasExactColimitsOfShape ℕ A]
    [PreservesColimit (Discrete.functor K.obj) H]
    [PreservesColimit (Discrete.functor (fun n : ℕ ↦ (K.obj n)⟦(1 : ℤ)⟧)) H] :
    Nonempty (IsColimit (imageCocone P H)) := sorry

end ImageCocone

namespace ImageComparison

/-- The image comparison is an isomorphism when the images of the explicitly retained
coproduct cocone and its shift by one are colimiting. -/
@[stacks 0CRK]
theorem isIso (P : Presentation K X) (H : D ⥤ A)
    [HasColimitsOfShape ℕ A] [IsTriangulated D] [Abelian A]
    [Functor.IsHomological H] [HasExactColimitsOfShape ℕ A]
    (h_coproduct : Nonempty (IsColimit (H.mapCocone P.coproduct.cocone)))
    (h_shifted_coproduct : Nonempty (IsColimit
      (H.mapCocone ((shiftFunctor D (1 : ℤ)).mapCocone P.coproduct.cocone)))) :
    IsIso (imageComparison P H) := sorry

end ImageComparison

/-- Stacks 0CRK, Lemma 13.33.8: the image comparison is an isomorphism when the
homological functor preserves the coproducts of the diagram terms and their shifts by one. -/
@[stacks 0CRK]
instance imageComparison_isIso (P : Presentation K X) (H : D ⥤ A)
    [HasColimitsOfShape ℕ A] [IsTriangulated D] [Abelian A]
    [Functor.IsHomological H] [HasExactColimitsOfShape ℕ A]
    [PreservesColimit (Discrete.functor K.obj) H]
    [PreservesColimit (Discrete.functor (fun n : ℕ ↦ (K.obj n)⟦(1 : ℤ)⟧)) H] :
    IsIso (imageComparison P H) := sorry

end CategoryTheory.HomotopyColimit.Presentation

end
