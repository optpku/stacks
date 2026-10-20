module

public import ReasLib.CategoryTheory.Functor.Derived.Composition.Left
public import ReasLib.CategoryTheory.ObjectProperty.Localization.FullSubcategory
public import Mathlib.CategoryTheory.Localization.Resolution

@[expose] public section

/-!
# Left-Derived Composition from Full-Subcategory Resolutions

This leaf upgrades the componentwise comparison theorem for chosen left-derived models to a
natural isomorphism.  The minimal criterion checks the iterated and direct counits on a full
subcategory admitting left resolutions; a factorwise criterion checks the two constituent
counits separately.
-/

universe vA vB vC vDA vDB uA uB uC uDA uDB

namespace CategoryTheory.Functor.LeftDerived.Composition.FullSubcategory

variable {A : Type uA} {B : Type uB} {C : Type uC}
  {DA : Type uDA} {DB : Type uDB}
  [Category.{vA} A] [Category.{vB} B] [Category.{vC} C]
  [Category.{vDA} DA] [Category.{vDB} DB]
  {F : A ⥤ B} {G : B ⥤ C} {L : A ⥤ DA} {L' : B ⥤ DB}
  {LF : DA ⥤ DB} {LG : DB ⥤ C} {LGF : DA ⥤ C}

/-- Stacks 05T2: if a full subcategory supplies left resolutions and both the iterated
counit and the direct-model counit are invertible on it, then the canonical comparison from
the iterated model to the direct left-derived model is an isomorphism. -/
@[stacks 05T2 "left-derived composition from an invertible iterated counit"]
theorem isIso_of_iteratedCounit
    (S : MorphismProperty A) (P : ObjectProperty A)
    [(fullSubcategoryLocalizerMorphism P S).HasLeftResolutions]
    (εF : L ⋙ LF ⟶ F ⋙ L') (εG : L' ⋙ LG ⟶ G)
    (εGF : L ⋙ LGF ⟶ F ⋙ G)
    [L.IsLocalization S] [LGF.IsLeftDerivedFunctor εGF S]
    (h_iterated : ∀ X : A, P X → IsIso ((iteratedCounit εF εG).app X))
    (hGF : ∀ X : A, P X → IsIso (εGF.app X)) :
    IsIso (comparisonOfModels S εF εG εGF) := by
  rw [(fullSubcategoryLocalizerMorphism P S).isIso_iff_of_hasLeftResolutions L]
  intro X
  letI := hGF X.obj X.property
  exact (comparisonOfModels_app_isIso_iff S εF εG εGF X.obj).2
    (h_iterated X.obj X.property)

set_option backward.isDefEq.respectTransparency false in
/-- Stacks 05T2: if a full subcategory supplies left resolutions and the counits for two
chosen left-derived models and their composite are invertible on it, then the canonical
comparison from the iterated model to the composite model is an isomorphism. This is the
factorwise specialization of `isIso_of_iteratedCounit`. -/
@[stacks 05T2 "left-derived composition from full-subcategory resolutions"]
theorem isIso
    (S : MorphismProperty A) (P : ObjectProperty A)
    [(fullSubcategoryLocalizerMorphism P S).HasLeftResolutions]
    (εF : L ⋙ LF ⟶ F ⋙ L') (εG : L' ⋙ LG ⟶ G)
    (εGF : L ⋙ LGF ⟶ F ⋙ G)
    [L.IsLocalization S] [LGF.IsLeftDerivedFunctor εGF S]
    (hF : ∀ X : A, P X → IsIso (εF.app X))
    (hG : ∀ X : A, P X → IsIso (εG.app (F.obj X)))
    (hGF : ∀ X : A, P X → IsIso (εGF.app X)) :
    IsIso (comparisonOfModels S εF εG εGF) := by
  apply isIso_of_iteratedCounit S P εF εG εGF _ hGF
  intro X hX
  rw [iteratedCounit_app]
  letI := hF X hX
  letI := hG X hX
  infer_instance

end CategoryTheory.Functor.LeftDerived.Composition.FullSubcategory
