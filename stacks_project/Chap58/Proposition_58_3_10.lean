module

public import ReasLib.CategoryTheory.Galois.Equivalence
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open PreGaloisCategory

universe u v w

/- Proposition 58.3.10: Let (C, F) be a Galois category. Let G = Aut(F) be as in
Example 58.3.5. The functor F : C ⟶ Finite-G-Sets (58.3.5.1), realized as
functorToContAction F : C ⥤ ContAction FintypeCat (Aut F), is an equivalence. -/
@[stacks 0BN4]
#check
  (CategoryTheory.PreGaloisCategory.functorToContAction_isEquivalence :
    ∀ {C : Type u} [Category.{v} C] (F : C ⥤ FintypeCat.{w})
      [GaloisCategory C] [FiberFunctor F], (functorToContAction F).IsEquivalence)

#check PreGaloisCategory.functorToContAction
