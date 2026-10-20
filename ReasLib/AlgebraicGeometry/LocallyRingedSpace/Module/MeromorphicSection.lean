/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.MeromorphicFunction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Restriction
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Stalk
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Meromorphic sections of module sheaves

For a module sheaf on a locally ringed space, extension of scalars from the structure sheaf to the
sheaf of meromorphic functions produces its sheaf of meromorphic sections. Meromorphic sections
are the global sections of that extended module sheaf.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable (X : LocallyRingedSpace.{u})

/-- The same-site `RingCat`-valued structure map underlying
`𝒪_X ⟶ 𝒦_X`. -/
@[stacks 01X4 "meromorphic function ring-sheaf map"]
abbrev toMeromorphicFunctionRingSheafMap :
    ringSheaf (Opens.grothendieckTopology X.toTopCat) X.𝒪 ⟶
      ((𝟭 (Opens X.toTopCat)).sheafPushforwardContinuous RingCat.{u}
        (Opens.grothendieckTopology X.toTopCat)
        (Opens.grothendieckTopology X.toTopCat)).obj
          (ringSheaf (Opens.grothendieckTopology X.toTopCat) (meromorphicFunctionSheaf X)) :=
  ringedSiteStructureMap
    (C := Opens X.toTopCat)
    (J := Opens.grothendieckTopology X.toTopCat)
    (𝒪 := X.𝒪)
    (𝒪' := meromorphicFunctionSheaf X)
    X.toMeromorphicFunctionSheafHom

/-- Extension of scalars along `𝒪_X ⟶ 𝒦_X`. -/
@[stacks 01X4 "meromorphic-section functor"]
noncomputable abbrev meromorphicSectionSheafFunctor :
    ringedSiteModuleCategory (Opens.grothendieckTopology X.toTopCat) X.𝒪 ⥤
      ringedSiteModuleCategory (Opens.grothendieckTopology X.toTopCat)
        (meromorphicFunctionSheaf X) :=
  SheafOfModules.pullback.{u} (toMeromorphicFunctionRingSheafMap X)

/-- For an `𝒪_X`-module sheaf `ℱ`, its sheaf of meromorphic sections is obtained
by extension of scalars along the canonical map `𝒪_X ⟶ 𝒦_X`. -/
@[stacks 01X4 "meromorphic-section sheaf"]
noncomputable abbrev meromorphicSectionSheaf
    (ℱ : ringedSiteModuleCategory (Opens.grothendieckTopology X.toTopCat) X.𝒪) :
    ringedSiteModuleCategory (Opens.grothendieckTopology X.toTopCat)
      (meromorphicFunctionSheaf X) :=
  (X.meromorphicSectionSheafFunctor).obj ℱ

/-- The sheaf `X.meromorphicSectionSheaf ℱ` is defined by extension of scalars along
`𝒪_X ⟶ 𝒦_X`. -/
@[simp]
theorem meromorphicSectionSheaf_eq_pullback
    (ℱ : ringedSiteModuleCategory (Opens.grothendieckTopology X.toTopCat) X.𝒪) :
    X.meromorphicSectionSheaf ℱ =
      (SheafOfModules.pullback.{u} (toMeromorphicFunctionRingSheafMap X)).obj ℱ := rfl

/-- The canonical map from the stalk of an `𝒪_X`-module to the stalk of its
meromorphic scalar extension. -/
noncomputable def meromorphicSectionStalkMap
    (ℱ : ringedSiteModuleCategory (Opens.grothendieckTopology X.toTopCat) X.𝒪)
    (x : X) :
    (SheafOfModules.stalkFunctorOfCommRing X.𝒪 x).obj ℱ →
      (SheafOfModules.stalkFunctorOfCommRing (meromorphicFunctionSheaf X) x).obj
        (X.meromorphicSectionSheaf ℱ) :=
  let adjunction :
      SheafOfModules.ChangeOfRings.extendScalars.{u, u, u, u}
          (ringSheafMap.{u, u, u} X.toMeromorphicFunctionSheafHom) ⊣
        restrictionAlong.{u, u, u, u} X.toMeromorphicFunctionSheafHom :=
    SheafOfModules.ChangeOfRings.extendRestrictAdjunction.{u, u, u, u}
      (ringSheafMap.{u, u, u} X.toMeromorphicFunctionSheafHom)
  let comparison :
      SheafOfModules.pullback (toMeromorphicFunctionRingSheafMap X) ≅
        SheafOfModules.ChangeOfRings.extendScalars.{u, u, u, u}
          (ringSheafMap.{u, u, u} X.toMeromorphicFunctionSheafHom) :=
    SheafOfModules.ChangeOfRings.pullbackIso.{u, u, u, u}
      (ringSheafMap.{u, u, u} X.toMeromorphicFunctionSheafHom)
  ((SheafOfModules.stalkFunctorOfCommRing X.𝒪 x).map
    (adjunction.unit.app ℱ ≫
      (restrictionAlong.{u, u, u, u} X.toMeromorphicFunctionSheafHom).map
        (comparison.inv.app ℱ))).hom

set_option maxHeartbeats 800000 in
/-- A meromorphic section of an `𝒪_X`-module sheaf is a global section of its
meromorphic-section sheaf. -/
@[stacks 01X4 "meromorphic sections"]
abbrev meromorphicSections
    (ℱ : ringedSiteModuleCategory (Opens.grothendieckTopology X.toTopCat) X.𝒪) : Type _ :=
  (X.meromorphicSectionSheaf ℱ).sections

/-- Meromorphic sections of `ℱ` are the global sections of `X.meromorphicSectionSheaf ℱ`. -/
@[simp]
theorem meromorphicSections_eq_sections
    (ℱ : ringedSiteModuleCategory (Opens.grothendieckTopology X.toTopCat) X.𝒪) :
    X.meromorphicSections ℱ = (X.meromorphicSectionSheaf ℱ).sections := rfl

end AlgebraicGeometry.LocallyRingedSpace
