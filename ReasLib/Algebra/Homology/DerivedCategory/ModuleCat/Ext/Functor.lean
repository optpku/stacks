/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Module-valued derived Ext functors

For a fixed object `K` of the derived category of modules, integer-degree derived Ext is naturally
an `A`-module-valued functor in the second variable.  This file owns that functor independently of
any ideal-power application.
@stack 0DYI
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace CategoryTheory.DerivedCategory.Ext

variable {A : Type u} [CommRing A] [HasDerivedCategory (ModuleCat A)]

/-- The `A`-linear functor `M ↦ Ext^i_A(K, M)` for an integer degree `i` and fixed derived
source `K`.

The common universe is inherited from Mathlib's standard derived category of `ModuleCat A` and
its endomorphism-ring-valued coyoneda functor. -/
@[stacks 0DYI "module-valued derived Ext functor"]
noncomputable abbrev moduleFunctor
    (K : DerivedCategory (ModuleCat A)) (i : ℤ) :
    ModuleCat A ⥤ ModuleCat A :=
  DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ) ⋙
    shiftFunctor _ i ⋙
    preadditiveCoyonedaObj K ⋙
    ModuleCat.restrictScalars (algebraMap A (End K)ᵐᵒᵖ)

end CategoryTheory.DerivedCategory.Ext
