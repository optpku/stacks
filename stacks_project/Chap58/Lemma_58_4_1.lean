/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.GaloisFunctorDiagram
import StacksCheckRecall

@[expose] public section

universe uC vC uC' vC' uC'' vC'' w

open CategoryTheory
open CategoryTheory.Limits

/- Lemma 58.4.1 -/
@[stacks 0BN6] #check
  (CategoryTheory.GaloisFunctorDiagram.tfae :
    ∀ {C : Type uC} [Category.{vC} C] [CategoryTheory.GaloisCategory C]
      {C' : Type uC'} [Category.{vC'} C'] [CategoryTheory.GaloisCategory C']
      {C'' : Type uC''} [Category.{vC''} C''] [CategoryTheory.GaloisCategory C'']
      {F : C ⥤ FintypeCat.{w}} [CategoryTheory.PreGaloisCategory.FiberFunctor F]
      {F' : C' ⥤ FintypeCat.{w}} [CategoryTheory.PreGaloisCategory.FiberFunctor F']
      {F'' : C'' ⥤ FintypeCat.{w}} [CategoryTheory.PreGaloisCategory.FiberFunctor F'']
      (D : CategoryTheory.GaloisFunctorDiagram F F' F''),
      List.TFAE [
        Function.Surjective D.h,
        Nonempty D.H.FullyFaithful,
        CategoryTheory.PreGaloisCategory.PreservesIsConnected D.H,
        ∀ X : C, CategoryTheory.PreGaloisCategory.IsConnected X →
          Nonempty (⊤_ C' ⟶ D.H.obj X) → Nonempty (⊤_ C ⟶ X),
        ∀ X : C, Function.Bijective (fun f : (⊤_ C ⟶ X) ↦
          (CategoryTheory.GaloisFunctorDiagram.isTerminal_obj_top D).from (⊤_ C') ≫
            D.H.map f)])
