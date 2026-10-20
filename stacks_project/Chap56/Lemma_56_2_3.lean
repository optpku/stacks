module

public import ReasLib.Algebra.Category.ModuleCat.FilteredColimitExtension.RightExact
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u v w z

namespace ModuleCat

/- Lemma 56.2.3 (1) -/
@[stacks 0GNL] #check (ModuleCat.filteredColimitExtension_of_rightExact_additive :
    ∀ {A : Type u} [Ring A] {B : Type w} [Category.{z} B]
      [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
      [HasFilteredColimitsOfSize.{max u v, max u v} B]
      (F : (ModuleCat.isFinitePresentation.{u, max u v} A).FullSubcategory ⥤ B)
      [PreservesFiniteColimits F]
      (F' : ModuleCat.{max u v} A ⥤ B)
      [PreservesFilteredColimitsOfSize.{max u v, max u v} F']
      (eF' : (ModuleCat.isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅ F), F'.Additive)

/- Lemma 56.2.3 (2) -/
@[stacks 0GNL] #check (ModuleCat.filteredColimitExtension_of_rightExact_preservesFiniteColimits :
    ∀ {A : Type u} [Ring A] {B : Type w} [Category.{z} B]
      [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
      [HasFilteredColimitsOfSize.{max u v, max u v} B]
      (F : (ModuleCat.isFinitePresentation.{u, max u v} A).FullSubcategory ⥤ B)
      [PreservesFiniteColimits F]
      (F' : ModuleCat.{max u v} A ⥤ B)
      [PreservesFilteredColimitsOfSize.{max u v, max u v} F']
      (eF' : (ModuleCat.isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅ F),
      PreservesFiniteColimits F')

/- Lemma 56.2.3 (3) -/
@[stacks 0GNL] #check (ModuleCat.filteredColimitExtension_of_rightExact_preservesCoproducts :
    ∀ {A : Type u} [Ring A] {B : Type w} [Category.{z} B]
      [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B]
      [HasFilteredColimitsOfSize.{max u v, max u v} B]
      (F : (ModuleCat.isFinitePresentation.{u, max u v} A).FullSubcategory ⥤ B)
      [PreservesFiniteColimits F]
      (F' : ModuleCat.{max u v} A ⥤ B)
      [PreservesFilteredColimitsOfSize.{max u v, max u v} F']
      (eF' : (ModuleCat.isFinitePresentation.{u, max u v} A).ι ⋙ F' ≅ F)
      (J : Type (max u v)), PreservesColimitsOfShape (Discrete J) F')

end ModuleCat
