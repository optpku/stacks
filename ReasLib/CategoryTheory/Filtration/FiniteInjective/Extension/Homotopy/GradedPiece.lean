module

public import ReasLib.CategoryTheory.Filtration.FiniteInjective.Extension.Homotopy.Basic
public import ReasLib.CategoryTheory.Filtration.FiniteInjective.GradedPiece
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Associated Graded Comparison for Homotopy Extensions

This leaf transports an extension's associated-graded comparison to bounded-below homotopy
categories. It exposes the comparison as a natural isomorphism together with its component and
naturality API, so applications need not unfold either bounded lifting or functor composition.
-/

@[expose] public section

open CategoryTheory

universe v₁ v₂ u₁ u₂

noncomputable section

namespace CategoryTheory.FilteredObject.Finite.FilteredInjective.Extension.Homotopy

variable {A : Type u₁} {B : Type u₂}
  [Category.{v₁} A] [Category.{v₂} B] [Abelian A] [Abelian B]

/-- The associated-graded comparison of a filtered extension, transported to bounded-below
homotopy categories. -/
@[stacks 05U1 "bounded-below associated-graded comparison"]
noncomputable def gradedIso {T : A ⥤+ B} (E : Extension T) (p : ℤ) :
    E.homotopy ⋙
        (FilteredObject.Finite.AssociatedGraded.functor B ⋙
          GradedObject.eval p).mapHomotopyCategoryPlus ≅
      (FilteredInjective.GradedPiece.functor (A := A) p).mapHomotopyCategoryPlus ⋙
        T.obj.mapHomotopyCategoryPlus :=
  Functor.mapHomotopyCategoryPlusCompIso (E.gradedIso p) ≪≫
    (Functor.mapHomotopyCategoryPlusCompIso
      (Iso.refl (FilteredInjective.GradedPiece.functor (A := A) p ⋙ T.obj))).symm

/-- The forward component of the homotopy associated-graded comparison is the composite of the
transported extension comparison and the canonical composition comparison. -/
@[simp, stacks 05U1 "bounded-below associated-graded comparison computation"]
theorem gradedIso_hom_app {T : A ⥤+ B} (E : Extension T) (p : ℤ)
    (K : HomotopyCategory.Plus (category A)) :
    (gradedIso E p).hom.app K =
      (Functor.mapHomotopyCategoryPlusCompIso (E.gradedIso p)).hom.app K ≫
        (Functor.mapHomotopyCategoryPlusCompIso
          (Iso.refl (FilteredInjective.GradedPiece.functor (A := A) p ⋙ T.obj))).inv.app K := sorry

/-- The inverse component of the homotopy associated-graded comparison is the reverse composite
of the canonical composition comparison and the transported extension comparison. -/
@[simp, stacks 05U1 "bounded-below associated-graded comparison computation"]
theorem gradedIso_inv_app {T : A ⥤+ B} (E : Extension T) (p : ℤ)
    (K : HomotopyCategory.Plus (category A)) :
    (gradedIso E p).inv.app K =
      (Functor.mapHomotopyCategoryPlusCompIso
          (Iso.refl (FilteredInjective.GradedPiece.functor (A := A) p ⋙ T.obj))).hom.app K ≫
        (Functor.mapHomotopyCategoryPlusCompIso (E.gradedIso p)).inv.app K := sorry

/-- Forward naturality of the bounded-below associated-graded comparison. -/
@[reassoc (attr := simp), stacks 05U1 "bounded-below associated-graded comparison naturality"]
theorem gradedIso_hom_naturality {T : A ⥤+ B} (E : Extension T) (p : ℤ)
    {K L : HomotopyCategory.Plus (category A)} (f : K ⟶ L) :
    (E.homotopy ⋙
          (FilteredObject.Finite.AssociatedGraded.functor B ⋙
            GradedObject.eval p).mapHomotopyCategoryPlus).map f ≫
        (gradedIso E p).hom.app L =
      (gradedIso E p).hom.app K ≫
        ((FilteredInjective.GradedPiece.functor (A := A) p).mapHomotopyCategoryPlus ⋙
          T.obj.mapHomotopyCategoryPlus).map f := sorry

/-- Inverse naturality of the bounded-below associated-graded comparison. -/
@[reassoc (attr := simp), stacks 05U1 "bounded-below associated-graded comparison naturality"]
theorem gradedIso_inv_naturality {T : A ⥤+ B} (E : Extension T) (p : ℤ)
    {K L : HomotopyCategory.Plus (category A)} (f : K ⟶ L) :
    ((FilteredInjective.GradedPiece.functor (A := A) p).mapHomotopyCategoryPlus ⋙
          T.obj.mapHomotopyCategoryPlus).map f ≫
        (gradedIso E p).inv.app L =
      (gradedIso E p).inv.app K ≫
        (E.homotopy ⋙
          (FilteredObject.Finite.AssociatedGraded.functor B ⋙
            GradedObject.eval p).mapHomotopyCategoryPlus).map f := sorry

end CategoryTheory.FilteredObject.Finite.FilteredInjective.Extension.Homotopy
