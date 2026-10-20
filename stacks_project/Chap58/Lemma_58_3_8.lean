module

public import ReasLib.CategoryTheory.Galois.Decomposition
import StacksCheckRecall

@[expose] public section

universe u v w

open CategoryTheory

/- Lemma 58.3.8: In a Galois category with fiber functor F, every connected
object X admits a morphism from a Galois object. -/
@[stacks 0BN2]
#check (CategoryTheory.PreGaloisCategory.exists_galois_object_hom_of_connected :
  ∀ {C : Type u} [Category.{v} C] [GaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) [PreGaloisCategory.FiberFunctor F] (X : C)
    [PreGaloisCategory.IsConnected X],
    ∃ (A : C) (_ : A ⟶ X), PreGaloisCategory.IsGalois A)

end
