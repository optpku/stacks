/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.RHom.IdealQuotient.Duality

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open RingedSpace TopologicalSpace
open DerivedCategory ModuleDerived
open CategoryTheory.MonoidalCategory
open MonoidalClosed
open ExteriorPower

noncomputable section

universe u

/- Lemma 48.15.5: if `I ⊆ 𝒪_Y` is Koszul-regular, then locally the derived dual of
`𝒪_Y / I` is the top exterior power of its conormal dual, shifted by the negative of
the positive minimal-generator rank. -/
@[stacks 0BQZ] #check
  (AlgebraicGeometry.RingedSpace.IdealSubobject.derivedDual_localIso :
    ∀ {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
      [KFlat.TensorDescends Y] [KFlat.IsLocalization Y]
      (H : MonoidalClosed (ModuleDerived Y)) (I : IdealSubobject Y)
      [IsKoszulRegularIdealSheaf I],
      ∀ y : Y, ∃ U : Opens Y, y ∈ U ∧
        let restrict := moduleRestrictionToOpenDerived Y U
        IsIsomorphic
          (restrict.obj
            (AlgebraicGeometry.RingedSpace.IdealSubobject.derivedDual H I))
          (restrict.obj
            (((singleFunctor Y.Modules 0).obj
              (ExteriorPower.sheaf
                (AlgebraicGeometry.RingedSpace.IdealSubobject.conormalDual I)
                (AlgebraicGeometry.RingedSpace.IdealSubobject.generatorRank I y)))
                ⟦(-(AlgebraicGeometry.RingedSpace.IdealSubobject.generatorRank I y : ℤ))⟧)))
