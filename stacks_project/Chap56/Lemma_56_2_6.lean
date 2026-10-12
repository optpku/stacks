/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Category.ModuleCat.FilteredColimitExtension.Coproducts
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty

universe u w z

/- Lemma 56.2.6 -/
@[stacks 0GNQ]
#check
  (CategoryTheory.ModuleCat.rightExactCoproductPreservingFunctorEquivalenceModuleAction :
    ∀ {A : Type u} [Ring A] {B : Type w} [Category.{z} B]
      [Preadditive B] [HasFiniteBiproducts B] [HasCokernels B] [HasCoproducts.{u} B],
      ∃ e :
        CategoryTheory.ModuleCat.RightExactCoproductPreservingFunctor A B ≌
          (SingleObj A ⥤+ B),
        ∀ (F : CategoryTheory.ModuleCat.RightExactCoproductPreservingFunctor A B),
          let KF := (e.functor.obj F).obj
          let FA := F.obj.obj
          ∃ i : KF.obj (SingleObj.star A) ≅
              FA.obj (ModuleCat.of Aᵐᵒᵖ A),
            ∀ a : A,
              KF.map a ≫ i.hom =
                i.hom ≫ FA.map
                  (ModuleCat.ofHom (LinearMap.mulLeft Aᵐᵒᵖ a)))
