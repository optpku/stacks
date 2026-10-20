module

public import Mathlib.CategoryTheory.Abelian.Basic
import StacksCheckRecall

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

section Pullback

variable {X Y Z : C} (a : X ⟶ Y) (b : Z ⟶ Y)

/- Example 12.5.6 (1): the canonical map from `pullback a b` to `X ⊞ Z` exhibits the
pullback as the kernel of `biprod.desc a (-b)`. -/
@[stacks 05PJ] #check
  (Abelian.PullbackToBiproductIsKernel.isLimitPullbackToBiproduct a b :
    IsLimit (Abelian.PullbackToBiproductIsKernel.pullbackToBiproductFork a b))

end Pullback

section Pushout

variable {X Y Z : C} (a : Y ⟶ X) (b : Y ⟶ Z)

/- Example 12.5.6 (2): the canonical map from `X ⊞ Z` to `pushout a b` exhibits the
pushout as the cokernel of `biprod.lift a (-b)`. -/
#check
  (Abelian.BiproductToPushoutIsCokernel.isColimitBiproductToPushout a b :
    IsColimit (Abelian.BiproductToPushoutIsCokernel.biproductToPushoutCofork a b))

end Pushout

end CategoryTheory
