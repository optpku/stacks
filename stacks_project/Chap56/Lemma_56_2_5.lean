module

public import ReasLib.Algebra.Category.ModuleCat.FinitePresentation.RightExact
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u w z

/- Lemma 56.2.5 -/
@[stacks 0GNN]
#check
  (CategoryTheory.ModuleCat.rightExactFunctorEquivalenceModuleAction :
    ∀ {A : Type u} [Ring A] {B : Type w} [Category.{z} B]
      [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B],
      let A₀ : (ModuleCat.isFinitePresentation.{u, u} Aᵐᵒᵖ).FullSubcategory :=
        ⟨ModuleCat.of Aᵐᵒᵖ A, Module.FinitePresentation.rightRegular A⟩
      ∃ e :
        ((ModuleCat.isFinitePresentation.{u, u} Aᵐᵒᵖ).FullSubcategory ⥤ᵣ B) ≌
          (SingleObj A ⥤+ B),
        ∀ (F : (ModuleCat.isFinitePresentation.{u, u} Aᵐᵒᵖ).FullSubcategory ⥤ᵣ B),
          ∃ i : (e.functor.obj F).obj.obj (SingleObj.star A) ≅ F.obj.obj A₀,
            ∀ a : A,
              (e.functor.obj F).obj.map a ≫ i.hom =
                i.hom ≫ F.obj.map (ObjectProperty.homMk
                  (ModuleCat.ofHom (LinearMap.mulLeft Aᵐᵒᵖ a))))
