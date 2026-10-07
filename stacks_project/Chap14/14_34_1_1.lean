module

public import Mathlib.CategoryTheory.Adjunction.Basic
import StacksCheckRecall

/-!
@stack 08NB
-/

@[expose] public section

universe uC uD vC vD

namespace CategoryTheory

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

/- 14.34.1.1 (1) is the right triangle identity of an adjunction. -/
@[stacks 08NB "14.34.1.1 (1)"]
#check (adj.right_triangle :
  Functor.whiskerLeft G adj.unit ≫ (Functor.associator G F G).inv ≫
      Functor.whiskerRight adj.counit G =
    G.rightUnitor.hom ≫ G.leftUnitor.inv)

/- 14.34.1.1 (2) is the left triangle identity of an adjunction. -/
@[stacks 08NB "14.34.1.1 (2)"]
#check (adj.left_triangle :
  Functor.whiskerRight adj.unit F ≫ (Functor.associator F G F).hom ≫
      Functor.whiskerLeft F adj.counit =
    F.leftUnitor.hom ≫ F.rightUnitor.inv)

end CategoryTheory
