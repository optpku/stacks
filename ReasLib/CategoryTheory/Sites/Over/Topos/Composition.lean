module

public import ReasLib.CategoryTheory.Sites.Over.Topos

/-!
# Composition of morphisms of topoi on slice sites

This module records the compatibility of the morphisms of topoi induced by
postcomposition on slice sites with composition in the ambient category.
-/

@[expose] public section

open CategoryTheory
open scoped MorphismOfTopoiIn

noncomputable section

universe uC vC w

namespace CategoryTheory.Over.Site

variable {C : Type uC} [Category.{vC} C]

/-- Morphisms of topoi induced by postcomposition on slice sites respect composition. -/
theorem morphismOfTopoi_comp (J : GrothendieckTopology C)
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Functor.IsContinuous (mapFunctor f) (J.over X) (J.over Y)]
    [Functor.IsCocontinuous (mapFunctor f) (J.over X) (J.over Y)]
    [HasWeakSheafify (J.over Y) (Type w)]
    [∀ P : (Over X)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasLeftKanExtension P]
    [∀ P : (Over X)ᵒᵖ ⥤ Type w, (mapFunctor f).op.HasPointwiseRightKanExtension P]
    [Functor.IsContinuous (mapFunctor g) (J.over Y) (J.over Z)]
    [Functor.IsCocontinuous (mapFunctor g) (J.over Y) (J.over Z)]
    [HasWeakSheafify (J.over Z) (Type w)]
    [∀ P : (Over Y)ᵒᵖ ⥤ Type w, (mapFunctor g).op.HasLeftKanExtension P]
    [∀ P : (Over Y)ᵒᵖ ⥤ Type w, (mapFunctor g).op.HasPointwiseRightKanExtension P]
    [Functor.IsContinuous (mapFunctor (f ≫ g)) (J.over X) (J.over Z)]
    [Functor.IsCocontinuous (mapFunctor (f ≫ g)) (J.over X) (J.over Z)]
    [∀ P : (Over X)ᵒᵖ ⥤ Type w, (mapFunctor (f ≫ g)).op.HasLeftKanExtension P]
    [∀ P : (Over X)ᵒᵖ ⥤ Type w,
      (mapFunctor (f ≫ g)).op.HasPointwiseRightKanExtension P] :
    MorphismOfTopoiIn.comp (morphismOfTopoi J g) (morphismOfTopoi J f) =
      morphismOfTopoi J (f ≫ g) := sorry

end CategoryTheory.Over.Site
