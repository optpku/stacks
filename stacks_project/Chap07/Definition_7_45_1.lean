/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Presheaf.Basic
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.Types.Products
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe u v w

variable {C : Type u} [Category.{v} C] (F : Presheaf C)

/- Definition 7.45.1: the global sections of a presheaf of sets F on a site C
(which need not have a final object) is the set Γ(C, F) = Mor_PSh(C)(*, F),
where * is the final object of PSh(C), i.e. the singleton-valued presheaf.
This is F.sections; equivalently Hom from the constant singleton presheaf
(Functor.const Cᵒᵖ).obj (PUnit : Type w). -/
@[stacks 06UN] #check (F.sections)

#check (F.sectionsEquivHom (PUnit : Type w) :
  F.sections ≃ ((Functor.const Cᵒᵖ).obj (PUnit : Type w) ⟶ F))

#check (Functor.isTerminalConst Cᵒᵖ (Types.isTerminalPUnit : IsTerminal (PUnit : Type w)) :
  IsTerminal ((Functor.const Cᵒᵖ).obj (PUnit : Type w)))

#check (Functor.sectionsFunctor Cᵒᵖ : (Cᵒᵖ ⥤ Type w) ⥤ Type max u w)
