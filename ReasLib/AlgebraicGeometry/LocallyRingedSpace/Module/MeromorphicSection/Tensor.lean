/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.RegularMeromorphicSection
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Sections.Tensor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Pullback.Monoidal
public import ReasLib.Algebra.Category.ModuleCat.Presheaf.Sections

/-!
# Tensor products of meromorphic sections

Meromorphic scalar extension is strong monoidal.  This module uses its tensor comparison to
transport the pure tensor of two global meromorphic sections back to the scalar extension of the
tensor product module.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open SheafOfModules.RingedSite
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable (X : LocallyRingedSpace.{u})

/-- The tensor product of two meromorphic sections, transported through the canonical monoidal
comparison for extension of scalars to the meromorphic function sheaf. -/
noncomputable def meromorphicSectionTensor
    {L N : ringedSiteModuleCategory (Opens.grothendieckTopology X.toTopCat) X.𝒪}
    (s : X.meromorphicSections L) (t : X.meromorphicSections N) :
    X.meromorphicSections (L ⊗ N) :=
  SheafOfModules.sectionsMap
    (SheafOfModules.Pullback.tensorIso
      (𝟭 (Opens X.toTopCat))
      (X.toMeromorphicFunctionSheafHom ≫
        (Functor.sheafPushforwardContinuousId CommRingCat
          (Opens.grothendieckTopology X.toTopCat)).inv.app
            (meromorphicFunctionSheaf X)) L N).inv
    (RingedSpace.tensorSection
      (X :=
        { carrier := X.toTopCat
          presheaf := (meromorphicFunctionSheaf X).1
          IsSheaf := (meromorphicFunctionSheaf X).2 }) s t)

/-- The tensor of meromorphic sections is the ordinary pure tensor section transported by the
inverse monoidal comparison for meromorphic scalar extension. -/
theorem meromorphicSectionTensor_def
    {L N : ringedSiteModuleCategory (Opens.grothendieckTopology X.toTopCat) X.𝒪}
    (s : X.meromorphicSections L) (t : X.meromorphicSections N) :
    meromorphicSectionTensor X s t =
      SheafOfModules.sectionsMap
        (SheafOfModules.Pullback.tensorIso
          (𝟭 (Opens X.toTopCat))
          (X.toMeromorphicFunctionSheafHom ≫
            (Functor.sheafPushforwardContinuousId CommRingCat
              (Opens.grothendieckTopology X.toTopCat)).inv.app
                (meromorphicFunctionSheaf X)) L N).inv
        (RingedSpace.tensorSection
          (X :=
            { carrier := X.toTopCat
              presheaf := (meromorphicFunctionSheaf X).1
              IsSheaf := (meromorphicFunctionSheaf X).2 }) s t) :=
  rfl

/-- The tensor product of regular meromorphic sections of invertible modules is regular. -/
theorem isRegularMeromorphicSection_tensor
    {L N : ringedSiteModuleCategory (Opens.grothendieckTopology X.toTopCat) X.𝒪}
    [isInvertibleObject L] [isInvertibleObject N]
    (s : X.meromorphicSections L) (t : X.meromorphicSections N)
    (hs : X.IsRegularMeromorphicSection L s)
    (ht : X.IsRegularMeromorphicSection N t) :
    X.IsRegularMeromorphicSection (L ⊗ N) (meromorphicSectionTensor X s t) := sorry

end AlgebraicGeometry.LocallyRingedSpace
