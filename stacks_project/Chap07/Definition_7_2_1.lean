module

public import ReasLib.CategoryTheory.Presheaf.Basic
public import Mathlib.CategoryTheory.Functor.Category
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u v w

variable (C : Type u) [Category.{v} C]

/- Definition 7.2.1: a presheaf of sets on C is a contravariant functor from C
to Sets. Morphisms of presheaves are transformations of functors. The category
of presheaves of sets is denoted PSh(C). This is the Type-valued functor
Presheaf C, i.e. Cᵒᵖ ⥤ Type w, with morphisms NatTrans and the functor-category
instance Functor.category. -/
@[stacks 00V2] #check Presheaf C

#check (Cᵒᵖ ⥤ Type w)
#check (inferInstance : Category (Presheaf C))
#check NatTrans
