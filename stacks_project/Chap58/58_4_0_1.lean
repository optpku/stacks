/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.CategoryTheory.GaloisFunctorDiagram
import StacksCheckRecall

universe uC vC uC' vC' uC'' vC'' w

open CategoryTheory
open CategoryTheory.PreGaloisCategory

/- 58.4.0.1: The chain of two 2-commutative squares associated to exact functors of Galois categories. -/
@[stacks 0BTR] #check (CategoryTheory.GaloisFunctorDiagram :
  {C : Type uC} → [Category.{vC} C] → [GaloisCategory C] →
  {C' : Type uC'} → [Category.{vC'} C'] → [GaloisCategory C'] →
  {C'' : Type uC''} → [Category.{vC''} C''] → [GaloisCategory C''] →
  (F : C ⥤ FintypeCat.{w}) → [FiberFunctor F] →
  (F' : C' ⥤ FintypeCat.{w}) → [FiberFunctor F'] →
  (F'' : C'' ⥤ FintypeCat.{w}) → [FiberFunctor F''] → Type _)
