/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap58.«58_4_0_1_Diagram»
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe uC vC uC' vC' uC'' vC'' w

/- Lemma 58.4.4 -/
@[stacks 0BN7] #check
  (CategoryTheory.GaloisFunctorDiagram.h'_injective_iff :
    {C : Type uC} → [Category.{vC} C] → [CategoryTheory.GaloisCategory C] →
    {C' : Type uC'} → [Category.{vC'} C'] → [CategoryTheory.GaloisCategory C'] →
    {C'' : Type uC''} → [Category.{vC''} C''] → [CategoryTheory.GaloisCategory C''] →
    {F : C ⥤ FintypeCat.{w}} → [CategoryTheory.PreGaloisCategory.FiberFunctor F] →
    {F' : C' ⥤ FintypeCat.{w}} → [CategoryTheory.PreGaloisCategory.FiberFunctor F'] →
    {F'' : C'' ⥤ FintypeCat.{w}} → [CategoryTheory.PreGaloisCategory.FiberFunctor F''] →
    (D : CategoryTheory.GaloisFunctorDiagram F F' F'') →
    Function.Injective D.h' ↔
      ∀ (X'' : C'') [CategoryTheory.PreGaloisCategory.IsConnected X''],
        ∃ (X' : C') (Y'' : C'') (p : Y'' ⟶ X'')
          (q : Y'' ⟶ D.H'.obj X'), CategoryTheory.Epi p ∧ CategoryTheory.Mono q)
