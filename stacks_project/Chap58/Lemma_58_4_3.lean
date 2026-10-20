/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.GaloisFunctorDiagram
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory

universe uC vC uC' vC' uC'' vC'' w

/- Lemma 58.4.3 -/
@[stacks 0BS9] #check
  (CategoryTheory.GaloisFunctorDiagram.exactSequence_tfae :
    ∀ {C : Type uC} [Category.{vC} C] [GaloisCategory C]
      {C' : Type uC'} [Category.{vC'} C'] [GaloisCategory C']
      {C'' : Type uC''} [Category.{vC''} C''] [GaloisCategory C'']
      {F : C ⥤ FintypeCat.{w}} [FiberFunctor F]
      {F' : C' ⥤ FintypeCat.{w}} [FiberFunctor F']
      {F'' : C'' ⥤ FintypeCat.{w}} [FiberFunctor F'']
      (D : GaloisFunctorDiagram F F' F''),
      List.TFAE [
        Function.Surjective D.h ∧
          D.h.comp D.h' = 1 ∧
          MonoidHom.ker D.h.toMonoidHom =
            (Subgroup.normalClosure
              (MonoidHom.range D.h'.toMonoidHom : Set (Aut F'))).topologicalClosure,
        Nonempty D.H.FullyFaithful ∧
          D.H.essImage =
            (ObjectProperty.additiveClosure
              (fun X : C'' ↦ Nonempty (IsTerminal X))).inverseImage D.H',
        Nonempty D.H.FullyFaithful ∧
          (⊤ : ObjectProperty C).map (D.H ⋙ D.H') ≤
            ObjectProperty.additiveClosure
              (fun X : C'' ↦ Nonempty (IsTerminal X)) ∧
          ∀ X' : C',
            ObjectProperty.additiveClosure
                (fun X : C'' ↦ Nonempty (IsTerminal X)) (D.H'.obj X') →
              ∃ (X : C) (f : D.H.obj X ⟶ X'), Epi f])
