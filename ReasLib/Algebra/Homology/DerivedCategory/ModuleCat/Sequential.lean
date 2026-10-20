/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
public import ReasLib.CategoryTheory.InverseSystem.Sequential

/-!
# Derived categories of sequential module systems

This leaf supplies the standard derived-category model for sequential inverse
systems of modules. It is deliberately specific to `ModuleCat`: generic
functor categories continue to receive a chosen derived-category model from
their callers.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.SequentialInverseSystem

/-- The standard derived-category structure on sequential inverse systems of modules over `R`. -/
instance moduleCatHasDerivedCategory (R : Type u) [Ring R] :
    HasDerivedCategory (SequentialInverseSystem (ModuleCat R)) :=
  HasDerivedCategory.standard (SequentialInverseSystem (ModuleCat R))

end CategoryTheory.SequentialInverseSystem
