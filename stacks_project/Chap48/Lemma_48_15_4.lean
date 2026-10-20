/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.RHom.IdealQuotient

@[expose] public section

open CategoryTheory
open AlgebraicGeometry
open RingedSpace
open DerivedCategory MonoidalClosed ModuleDerived

noncomputable section

universe u

/- Lemma 48.15.4: Let `Y` be a ringed space and `I ⊆ 𝒪_Y` a Koszul-regular ideal
sheaf. For `𝒪_X = 𝒪_Y / I`, composition on `RHom_{𝒪_Y}(𝒪_X, 𝒪_X)` induces an
isomorphism from `ExteriorPower.sheaf (Ext¹_{𝒪_Y}(𝒪_X, 𝒪_X)) i` to
`Extⁱ_{𝒪_Y}(𝒪_X, 𝒪_X)` for every `i : ℕ`. -/
@[stacks 0BQY] #check
  (AlgebraicGeometry.RingedSpace.IdealSubobject.compositionExteriorPowerMap_isIso :
    ∀ {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
      [KFlat.TensorDescends Y] [KFlat.IsLocalization Y]
      (H : MonoidalClosed (ModuleDerived Y)) (I : IdealSubobject Y)
      [IsKoszulRegularIdealSheaf I] (i : ℕ),
      IsIso
        (AlgebraicGeometry.RingedSpace.IdealSubobject.compositionExteriorPowerMap H I i))
