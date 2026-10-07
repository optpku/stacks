module

public import ReasLib.CategoryTheory.Galois.Transitivity
import StacksCheckRecall

universe u v w

/- Lemma 58.3.9: Let (C, F) be a Galois category. Let G = Aut(F) be as in
Example 58.3.5. For any connected X in C the action of G on F(X) is
transitive. -/
@[stacks 0BN3]
#check (CategoryTheory.PreGaloisCategory.FiberFunctor.exists_aut_app_eq_of_isConnected :
  ∀ {C : Type u} [CategoryTheory.Category.{v} C] [CategoryTheory.GaloisCategory C]
    (F : CategoryTheory.Functor C FintypeCat.{w})
    [CategoryTheory.PreGaloisCategory.FiberFunctor F]
    (X : C) [CategoryTheory.PreGaloisCategory.IsConnected X] (x y : F.obj X),
    ∃ σ : CategoryTheory.Aut F, σ.hom.app X x = y)
