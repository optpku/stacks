/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.CategoryTheory.Filtered.EssentiallyConstant.FullSubcategory
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Comma.Final
public import ReasLib.CategoryTheory.Localization.LocalizerMorphism.Comma.Projection

/-!
# Essential constancy along localizer-morphism comma functors

Finality or initiality of the induced localization-comma functor can be combined directly with
its canonical projection comparison.  The resulting API transports essential constancy without
asking applications to reassociate functor compositions or compose natural isomorphisms by
hand.  A second layer also reflects through an arbitrary retract-closed full subcategory.
-/

@[expose] public section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.LocalizerMorphism

variable {C₁ : Type u₁} {C₂ : Type u₂} {D : Type u₃}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D]
  {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}

namespace costructuredArrow.EssentiallyConstant

/-- Stacks 05T5: essential constancy of a localization costructured-arrow diagram is detected
after restriction along a final localizer-morphism comma functor and transport across its
canonical source-projection comparison. -/
@[stacks 05T5 "essential constancy along a localizer-morphism costructured-arrow functor"]
theorem iff (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    [IsFiltered (CostructuredArrow W₁.Q (W₁.Q.obj X))]
    [Functor.Final (Φ.costructuredArrow X)] (F : C₂ ⥤ D) :
    IsFiltered.IsEssentiallyConstant
        (CostructuredArrow.proj W₂.Q (W₂.Q.obj (Φ.functor.obj X)) ⋙ F) ↔
      IsFiltered.IsEssentiallyConstant
        ((CostructuredArrow.proj W₁.Q (W₁.Q.obj X) ⋙ Φ.functor) ⋙ F) := sorry

/-- Stacks 05T5: combine final localization-comma restriction, its source-projection
comparison, and reflection through a retract-closed full subcategory in one step. -/
@[stacks 05T5 "essential constancy in a full subcategory along a costructured-arrow functor"]
theorem fullSubcategory_iff (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    [IsFiltered (CostructuredArrow W₁.Q (W₁.Q.obj X))]
    [Functor.Final (Φ.costructuredArrow X)] (P : ObjectProperty D)
    [P.IsStableUnderRetracts] (F : C₂ ⥤ D) (G : C₁ ⥤ P.FullSubcategory)
    (e : Φ.functor ⋙ F ≅ G ⋙ P.ι) :
    IsFiltered.IsEssentiallyConstant
        (CostructuredArrow.proj W₂.Q (W₂.Q.obj (Φ.functor.obj X)) ⋙ F) ↔
      IsFiltered.IsEssentiallyConstant
        (CostructuredArrow.proj W₁.Q (W₁.Q.obj X) ⋙ G) := sorry

end costructuredArrow.EssentiallyConstant

namespace structuredArrow.EssentiallyConstant

/-- Stacks 05T5: essential constancy of a localization structured-arrow diagram is detected
after restriction along an initial localizer-morphism comma functor and transport across its
canonical target-projection comparison. -/
@[stacks 05T5 "essential constancy along a localizer-morphism structured-arrow functor"]
theorem iff (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    [IsCofiltered (StructuredArrow (W₁.Q.obj X) W₁.Q)]
    [Functor.Initial (Φ.structuredArrow X)] (F : C₂ ⥤ D) :
    IsCofiltered.IsEssentiallyConstant
        (StructuredArrow.proj (W₂.Q.obj (Φ.functor.obj X)) W₂.Q ⋙ F) ↔
      IsCofiltered.IsEssentiallyConstant
        ((StructuredArrow.proj (W₁.Q.obj X) W₁.Q ⋙ Φ.functor) ⋙ F) := sorry

/-- Stacks 05T5: combine initial localization-comma restriction, its target-projection
comparison, and reflection through a retract-closed full subcategory in one step. -/
@[stacks 05T5 "essential constancy in a full subcategory along a structured-arrow functor"]
theorem fullSubcategory_iff (Φ : LocalizerMorphism W₁ W₂) (X : C₁)
    [IsCofiltered (StructuredArrow (W₁.Q.obj X) W₁.Q)]
    [Functor.Initial (Φ.structuredArrow X)] (P : ObjectProperty D)
    [P.IsStableUnderRetracts] (F : C₂ ⥤ D) (G : C₁ ⥤ P.FullSubcategory)
    (e : Φ.functor ⋙ F ≅ G ⋙ P.ι) :
    IsCofiltered.IsEssentiallyConstant
        (StructuredArrow.proj (W₂.Q.obj (Φ.functor.obj X)) W₂.Q ⋙ F) ↔
      IsCofiltered.IsEssentiallyConstant
        (StructuredArrow.proj (W₁.Q.obj X) W₁.Q ⋙ G) := sorry

end structuredArrow.EssentiallyConstant

end CategoryTheory.LocalizerMorphism
