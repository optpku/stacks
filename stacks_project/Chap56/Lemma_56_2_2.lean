module

public import ReasLib.Algebra.Category.ModuleCat.FilteredColimitExtension.Additive
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u v w z

/- Lemma 56.2.2 (1) -/
@[stacks 0GNK] #check (ModuleCat.filteredColimitExtension_additive :
    ∀ {A : Type u} [Ring A] {B : Type w} [Category.{z} B]
      [Preadditive B] [HasFiniteBiproducts B]
      [HasFilteredColimitsOfSize.{max u v, max u v} B]
      (F : (ModuleCat.isFinitePresentation.{u, max u v} A).FullSubcategory ⥤ B) [F.Additive]
      (F' : ModuleCat.{max u v} A ⥤ B)
      [PreservesFilteredColimitsOfSize.{max u v, max u v} F']
      (eF' : (ModuleCat.isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅ F), F'.Additive)

/- Lemma 56.2.2 (2) -/
@[stacks 0GNK] #check (ModuleCat.filteredColimitExtension_preservesCoproducts :
    ∀ {A : Type u} [Ring A] {B : Type w} [Category.{z} B]
      [Preadditive B] [HasFiniteBiproducts B]
      [HasFilteredColimitsOfSize.{max u v, max u v} B]
      (F : (ModuleCat.isFinitePresentation.{u, max u v} A).FullSubcategory ⥤ B) [F.Additive]
      (F' : ModuleCat.{max u v} A ⥤ B)
      [PreservesFilteredColimitsOfSize.{max u v, max u v} F']
      (eF' : (ModuleCat.isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅ F)
      (J : Type (max u v)), PreservesColimitsOfShape (Discrete J) F')
