/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.FlatBaseChange
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.WeightGrading

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace ModuleValuedFunctor.TensorAdequate

/-- A short exact extension of a tensor-extension functor by a tensor-linearly adequate
module-valued functor has a tensor-adequate middle term. -/
theorem of_shortExact_tensorExtension
    {A : CommRingCat.{u}} {M : ModuleCat.{u} A}
    {G L : ModuleValuedFunctor.bundled.{u, u} A}
    (i : (tensorExtensionFunctor A).obj M ⟶ G) (p : G ⟶ L)
    (h_zero : i ≫ p =
      (@HasZeroMorphisms.zero (ModuleValuedFunctor.bundled.{u, u} A)
        _ (ModuleValuedFunctor.bundledHasZeroMorphisms A)
        ((tensorExtensionFunctor A).obj M) L).zero)
    (h_short :
      @ShortComplex.ShortExact (ModuleValuedFunctor.bundled.{u, u} A) _
        (ModuleValuedFunctor.bundledHasZeroMorphisms A)
        (@ShortComplex.mk (ModuleValuedFunctor.bundled.{u, u} A) _
          (ModuleValuedFunctor.bundledHasZeroMorphisms A) _ _ _ i p h_zero))
    (hL : TensorLinearlyAdequate L) :
    TensorAdequate G := sorry

/-- Tensor-adequate module-valued functors are closed under short exact extensions. -/
theorem isClosedUnderExtensions (A : CommRingCat.{u}) :
    @ObjectProperty.IsClosedUnderExtensions
      (ModuleValuedFunctor.bundled.{u, u} A) _
      (TensorAdequate (A := A))
      (ModuleValuedFunctor.bundledHasZeroMorphisms A) := sorry

end ModuleValuedFunctor.TensorAdequate
