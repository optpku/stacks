/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.FinitePresentation
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Abelian
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.TensorExtension

@[expose] public section

open CategoryTheory

universe u

namespace ModuleValuedFunctor

/-- Positive-degree Ext groups from a finitely presented tensor-extension module
to any tensor-extension module are subsingleton in the bundled category. -/
@[stacks 06ZG]
theorem ext_tensorExtension_subsingleton (A : CommRingCat.{u})
    (M P : ModuleCat.{u} A) [Module.FinitePresentation A P]
    (i : ℕ) (hi : 0 < i) :
    Subsingleton (@Abelian.Ext _ (bundled.{u, u} A).str (bundledAbelian A)
      (bundledHasExt A) ((tensorExtensionFunctor A).obj P)
      ((tensorExtensionFunctor A).obj M) i) := sorry

/-- Every positive-degree Ext group from a tensor-linearly adequate functor to a
tensor-extension module is subsingleton in the bundled category. -/
theorem TensorLinearlyAdequate.ext_tensorExtension_subsingleton
    {A : CommRingCat.{u}} {L : bundled.{u, u} A}
    (hL : TensorLinearlyAdequate L) (M : ModuleCat.{u} A)
    (i : ℕ) (hi : 0 < i) :
    Subsingleton (@Abelian.Ext _ (bundled.{u, u} A).str (bundledAbelian A)
      (bundledHasExt A) L ((tensorExtensionFunctor A).obj M) i) := sorry

end ModuleValuedFunctor
