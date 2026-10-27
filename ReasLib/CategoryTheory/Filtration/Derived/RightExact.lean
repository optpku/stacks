/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.Filtration.ImageMap
public import ReasLib.CategoryTheory.Filtration.Derived.Projective
public import ReasLib.Algebra.Homology.HomotopyCategory.Bounded.Functor
public import ReasLib.CategoryTheory.Preadditive.RightExact
public import Mathlib.CategoryTheory.Limits.ExactFunctor

/-! Bounded-above filtered derived functors of right-exact functors. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
noncomputable section
universe v₁ v₂ u₁ u₂

namespace CategoryTheory.FilteredObject.FiniteDerived.Minus.RightExact

variable {A : Type u₁} {B : Type u₂}
  [_root_.CategoryTheory.Category.{v₁} A]
  [_root_.CategoryTheory.Category.{v₂} B]
  [Abelian A] [Abelian B]

/-- The bounded-above homotopy functor induced by applying a right-exact functor to finite
filtered-projective objects. Its source is the bounded-above homotopy category of finite filtered-projective objects. -/
noncomputable def homotopy (G : A ⥤ᵣ B) :
    HomotopyCategory.Minus (Finite.FilteredProjective.category A) ⥤
      HomotopyCategory.Minus (FilteredObject.Finite.category B) :=
  (Finite.FilteredProjective.inclusion A ⋙ Finite.imageMapFunctor G.obj).mapHomotopyCategoryMinus

/-- Objectwise computation for the bounded-above homotopy functor induced by `G`. -/
@[simp]
theorem homotopy_obj_obj (G : A ⥤ᵣ B)
    (K : HomotopyCategory.Minus (Finite.FilteredProjective.category A)) :
    ((homotopy G).obj K).obj =
      ((Finite.FilteredProjective.inclusion A ⋙ Finite.imageMapFunctor G.obj).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj K.obj := sorry

variable [HasDerivedCategory (GradedObject ℤ A)]
  [HasDerivedCategory (GradedObject ℤ B)]

/-- The filtered left-derived functor of a right-exact functor, obtained by transporting the
homotopy-level map along the canonical filtered-projective equivalence. -/
noncomputable def functor (G : A ⥤ᵣ B) [EnoughProjectives A]
    (hA : AssociatedGraded.Inverts A) (hB : AssociatedGraded.Inverts B) :
    Minus.Category A hA ⥤ Minus.Category B hB :=
  (Minus.FilteredProjective.equivalenceOf A hA
    (Minus.FilteredProjective.isEquivalence A hA)).inverse ⋙
    homotopy G ⋙ Minus.Quotient.functor B hB

/-- Unfolding of the filtered left-derived functor of a right-exact functor. -/
theorem functor_eq (G : A ⥤ᵣ B) [EnoughProjectives A]
    (hA : AssociatedGraded.Inverts A) (hB : AssociatedGraded.Inverts B) :
    functor G hA hB =
      (Minus.FilteredProjective.equivalenceOf A hA
        (Minus.FilteredProjective.isEquivalence A hA)).inverse ⋙
        homotopy G ⋙ Minus.Quotient.functor B hB := sorry

/-- Transporting the derived functor along the filtered-projective model agrees with the
homotopy-level image-filtration functor followed by localization. -/
noncomputable def diagramIso (G : A ⥤ᵣ B) [EnoughProjectives A]
    (hA : AssociatedGraded.Inverts A) (hB : AssociatedGraded.Inverts B) :
    Minus.FilteredProjective.functor A hA ⋙ functor G hA hB ≅
      homotopy G ⋙ Minus.Quotient.functor B hB :=
  (Minus.FilteredProjective.equivalenceOf A hA
    (Minus.FilteredProjective.isEquivalence A hA)).funInvIdAssoc
    (homotopy G ⋙ Minus.Quotient.functor B hB)

/-- Each component of the model comparison is the image of the inverse equivalence unit. -/
theorem diagramIso_hom_app (G : A ⥤ᵣ B) [EnoughProjectives A]
    (hA : AssociatedGraded.Inverts A) (hB : AssociatedGraded.Inverts B)
    (K : HomotopyCategory.Minus (Finite.FilteredProjective.category A)) :
    (diagramIso G hA hB).hom.app K =
      (homotopy G ⋙ Minus.Quotient.functor B hB).map
        ((Minus.FilteredProjective.equivalenceOf A hA
          (Minus.FilteredProjective.isEquivalence A hA)).unitInv.app K) :=
  sorry

end CategoryTheory.FilteredObject.FiniteDerived.Minus.RightExact

