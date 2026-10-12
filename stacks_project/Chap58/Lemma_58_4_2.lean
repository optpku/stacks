/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.GaloisFunctorDiagram
import StacksCheckRecall

@[expose] public section

open CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory

universe uC vC uC' vC' uC'' vC'' w

namespace CategoryTheory.GaloisFunctorDiagram

variable {C : Type uC} [Category.{vC} C] [GaloisCategory C]
variable {C' : Type uC'} [Category.{vC'} C'] [GaloisCategory C']
variable {C'' : Type uC''} [Category.{vC''} C''] [GaloisCategory C'']
variable {F : C ⥤ FintypeCat.{w}} [FiberFunctor F]
variable {F' : C' ⥤ FintypeCat.{w}} [FiberFunctor F']
variable {F'' : C'' ⥤ FintypeCat.{w}} [FiberFunctor F'']

/- Lemma 58.4.2 -/
@[stacks 0BS8]
#check (CategoryTheory.GaloisFunctorDiagram.comp_trivial_iff :
  {C : Type uC} → [Category.{vC} C] → [GaloisCategory C] →
  {C' : Type uC'} → [Category.{vC'} C'] → [GaloisCategory C'] →
  {C'' : Type uC''} → [Category.{vC''} C''] → [GaloisCategory C''] →
  {F : C ⥤ FintypeCat.{w}} → [FiberFunctor F] →
  {F' : C' ⥤ FintypeCat.{w}} → [FiberFunctor F'] →
  {F'' : C'' ⥤ FintypeCat.{w}} → [FiberFunctor F''] →
  (D : GaloisFunctorDiagram F F' F'') →
  D.h.comp D.h' = 1 ↔
    (⊤ : ObjectProperty C).map (D.H ⋙ D.H') ≤
      ObjectProperty.additiveClosure (fun X : C'' ↦ Nonempty (IsTerminal X)))

end CategoryTheory.GaloisFunctorDiagram
