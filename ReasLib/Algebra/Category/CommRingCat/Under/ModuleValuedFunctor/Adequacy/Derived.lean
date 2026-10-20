/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Abelian
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.Coreflection
public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.Injectives
public import ReasLib.CategoryTheory.DerivedCategory.Functor.Bounded.Acyclic.Characterization

@[expose] public section

open CategoryTheory CategoryTheory.Functor.RightDerived CategoryTheory.Limits

attribute [instance] ModuleValuedFunctor.bundledAbelian
attribute [instance] ModuleValuedFunctor.TensorAdequate.ambientEnoughInjectives
attribute [instance] ModuleValuedFunctor.TensorAdequate.inclusion_isLeftAdjoint
attribute [instance] ModuleValuedFunctor.TensorAdequate.isWeakSerreClass

universe u

namespace ModuleValuedFunctor.TensorAdequate

/-- The canonical right adjoint to the tensor-adequate inclusion is additive. -/
instance coreflectorAdditive (A : CommRingCat.{u}) :
    (ObjectProperty.ι (TensorAdequate (A := A))).rightAdjoint.Additive := sorry

/-- Every positive-degree right-derived value of the tensor-adequate coreflector
is zero on a tensor-adequate module-valued functor. -/
theorem coreflectorRightDerivedIsZero (A : CommRingCat.{u})
    {F : ModuleValuedFunctor.bundled.{u, u} A} (hF : TensorAdequate F)
    (p : ℕ) (hp : 0 < p) :
    IsZero
      ((((ObjectProperty.ι (TensorAdequate (A := A))).rightAdjoint).rightDerived p).obj F) := sorry

/-- The tensor-adequate coreflector has vanishing positive-degree right-derived
values on every tensor-adequate module-valued functor. -/
theorem coreflectorVanishesAboveZero (A : CommRingCat.{u})
    {F : ModuleValuedFunctor.bundled.{u, u} A} (hF : TensorAdequate F) :
    Vanishes.aboveZero
      (ObjectProperty.ι (TensorAdequate (A := A))).rightAdjoint F := sorry

end ModuleValuedFunctor.TensorAdequate
