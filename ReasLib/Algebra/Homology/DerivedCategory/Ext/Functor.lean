/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import ReasLib.Algebra.Homology.DerivedCategory.ModuleCat
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derived Ext as a functor of a module target

@stack 0G97

For a fixed derived `R`-module complex, integer-degree derived Ext is functorial in a module
placed in degree zero.  The additive-group-valued functor is the natural owner for hypotheses
about preserving monomorphisms or being a zero functor.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u v

namespace CategoryTheory.DerivedCategory.Ext

variable {R : Type u} [Ring R]

/-- The additive-group-valued functor `M ↦ Ext^i_R(K, M[0])`, for a fixed derived source `K`.
-/
@[stacks 0G97 "derived Ext in the module target"]
noncomputable abbrev addCommGrpFunctor
    (K : DerivedCategory (ModuleCat.{v, u} R)) (i : ℤ) :
    ModuleCat.{v, u} R ⥤ AddCommGrpCat :=
  DerivedCategory.singleFunctor (ModuleCat.{v, u} R) (0 : ℤ) ⋙
    shiftFunctor _ i ⋙
    preadditiveCoyonedaObj K ⋙
    forget₂ _ AddCommGrpCat

end CategoryTheory.DerivedCategory.Ext
