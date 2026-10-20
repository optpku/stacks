module

public import ReasLib.CategoryTheory.Functor.AutEmbedding
import StacksCheckRecall

@[expose] public section

universe u v w

namespace CategoryTheory

namespace Functor

variable {C : Type u} [Category.{v} C] (F : C ⥤ Type w)

/- 58.3.0.1: The canonical map from `Aut F` to the product of the objectwise
groups `Aut (F.obj X)` over all objects `X : C`. -/
@[stacks 0BS7] #check (CategoryTheory.Functor.autEmbedding F :
  Aut F → ∀ X : C, Aut (F.obj X))

end Functor

end CategoryTheory
