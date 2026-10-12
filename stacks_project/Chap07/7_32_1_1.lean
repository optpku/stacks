/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Functor.PresheafFiber
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u₁ v w

variable {C : Type u₁} [Category.{v} C] (u : C ⥤ Type w)
variable [Limits.HasColimitsOfShape u.Elementsᵒᵖ (Type w)]

/- 7.32.1.1: for any functor p = u : C ⥤ Type, the stalk of a presheaf F at p
is the colimit of F(U) over the opposite of the category of neighbourhoods
{(U, x)} with x ∈ u(U). Neighbourhoods of p are the objects of u.Elements; a
morphism (V, y) ⟶ (U, x) is α : V ⟶ U with u.map α y = x. The stalk functor
is u.presheafFiber, i.e. (whiskeringLeft).obj (π u).op ⋙ colim.

An element of F_p is a triple (U, x, s) with s ∈ F(U), modulo the generated
restriction relation; germs of such triples are recovered by toPresheafFiber. -/
@[stacks 04EH] #check (CategoryTheory.Functor.presheafFiber u : (Cᵒᵖ ⥤ Type w) ⥤ Type w)
