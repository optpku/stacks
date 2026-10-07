module

public import ReasLib.CategoryTheory.Functor.PresheafFiber
import StacksCheckRecall

@[expose] public section

open CategoryTheory

/- 7.32.3.1: for a functor u : C ⥤ Type and a set E, the presheaf u^p E is
defined by the object formula U ↦ Map(u(U), E). This is u.presheafCostalk:
(u.presheafCostalk.obj E).obj (op U) = (u.obj U → E). This defines a functor
u^p : Type ⥤ (Cᵒᵖ ⥤ Type). -/
@[stacks 04EI] #check @Functor.presheafCostalk
