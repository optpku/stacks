/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.Under.ModuleValuedFunctor.Adequacy.Derived
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Functor.RightDerived CategoryTheory.Limits

universe u

namespace ModuleValuedFunctor.TensorAdequate

/- Lemma 46.4.10 -/
@[stacks 06ZI] #check
  (ModuleValuedFunctor.TensorAdequate.coreflectorRightDerivedIsZero :
    ∀ (A : CommRingCat.{u})
      {F : ModuleValuedFunctor.bundled.{u, u} A}, TensorAdequate F →
      ∀ (p : ℕ), 0 < p →
        IsZero
          ((((ObjectProperty.ι (TensorAdequate (A := A))).rightAdjoint).rightDerived p).obj F))

#check
  (coreflectorVanishesAboveZero :
    ∀ (A : CommRingCat.{u})
      {F : ModuleValuedFunctor.bundled.{u, u} A}, TensorAdequate F →
      Vanishes.aboveZero
        (ObjectProperty.ι (TensorAdequate (A := A))).rightAdjoint F)

end ModuleValuedFunctor.TensorAdequate
