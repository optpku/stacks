/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Forgetting a commutative algebra to a module

Mathlib exposes the two individual forgetful functors through `AlgCat`.
This file names their composite so adjunctions and algebra constructions do
not repeatedly spell out that implementation path.
-/

@[expose] public section

open CategoryTheory

universe u v

namespace CommAlgCat

/-- The forgetful functor from commutative `R`-algebras to `R`-modules. -/
@[stacks 00DQ "forget a commutative algebra to a module"]
abbrev forgetToModule (R : Type u) [CommRing R] :
    CommAlgCat.{v} R ⥤ ModuleCat.{v} R :=
  forget₂ (CommAlgCat.{v} R) (AlgCat.{v} R) ⋙
    forget₂ (AlgCat.{v} R) (ModuleCat.{v} R)

end CommAlgCat
