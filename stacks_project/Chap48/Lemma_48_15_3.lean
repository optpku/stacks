/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.RHom.Conormal

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open RingedSpace
open SheafOfModules.RingedSite.InternalHom
open DerivedCategory MonoidalClosed ModuleDerived

noncomputable section

universe u

/- Lemma 48.15.3: for an ideal sheaf `I ⊆ 𝒪_Y`, the canonical comparison from
`Hom_𝒪_Y(I / I ^ 2, 𝒪_Y / I)` to `Ext^1_𝒪_Y(𝒪_Y / I, 𝒪_Y / I)` is an
isomorphism. -/
@[stacks 0BQW] #check
  (AlgebraicGeometry.RingedSpace.IdealSubobject.conormalExtOneComparison_isIso :
    ∀ {Y : RingedSpace.{u}} [KFlat.HomotopyTensorDescends Y]
      [KFlat.TensorDescends Y] [KFlat.IsLocalization Y]
      (H : MonoidalClosed (ModuleDerived Y)) (I : IdealSubobject Y)
      [((tensoringRight (ModuleDerived Y)).obj
        ((singleFunctor Y.Modules 0).obj
          (obj Y.sheaf (conormalModule I) (quotientStructureModule I)))).CommShift ℤ]
      [(ihomOf H ((singleFunctor Y.Modules 0).obj
        (quotientStructureModule I))).CommShift ℤ],
      IsIso
        (AlgebraicGeometry.RingedSpace.IdealSubobject.conormalExtOneComparison H I))
