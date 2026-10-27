/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Tensor
public import Mathlib.CategoryTheory.Monoidal.Preadditive

/-!
# Exactness properties of tensor products of module sheaves

This leaf records categorical infrastructure of the canonical tensor product on modules over a
commutative ring sheaf.  It is deliberately independent of flatness: additivity and right
exactness belong to tensor itself and should be reusable by every later homological development.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory

noncomputable section

universe u v w w' v'

namespace SheafOfModules.RingedSite

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
variable [HasWeakSheafify J AddCommGrpCat.{w}]
variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable {O : Sheaf J CommRingCat.{w}}

/-- The tensor product of modules over a commutative ring sheaf is additive in both variables. -/
@[stacks 03EP "additive tensor product on module sheaves"]
instance monoidalPreadditive :
    MonoidalPreadditive (ringedSiteModuleCategory.{u, v, w, w} J O) := sorry

namespace ModuleOver

/-- The direct `over` presentation of modules on `C / U` inherits the canonical additive
tensor product.  This is the preadditive counterpart of `ModuleOver.monoidalCategory`. -/
@[stacks 03EP "additive tensor product on a slice site", instance]
theorem monoidalPreadditive (O : Sheaf J CommRingCat.{w}) (U : C)
    [(J.over U).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}] :
    MonoidalPreadditive (SheafOfModules.{w} ((ringSheaf J O).over U)) := sorry

end ModuleOver

/-- Tensoring module sheaves on the right preserves finite colimits. -/
@[stacks 03EP "right tensor preserves finite colimits"]
instance tensorRightPreservesFiniteColimits
    (G : ringedSiteModuleCategory.{u, v, w, w} J O) :
    PreservesFiniteColimits (tensorRight G) := sorry

/-- Tensoring module sheaves on the right preserves binary biproducts. -/
instance tensorRightPreservesBinaryBiproducts
    (G : ringedSiteModuleCategory.{u, v, w, w} J O) :
    PreservesBinaryBiproducts (tensorRight G) := sorry

/-- Tensoring module sheaves on the left preserves colimits of shapes with `w`-small object types.
The size bound ensures that the underlying module-presheaf colimits exist pointwise; no size
bound on the base site or on the morphisms of the diagram shape is required. -/
@[stacks 03EP "left tensor preserves shaped colimits", instance]
theorem tensorLeftPreservesColimitsOfShape
    {K : Type*} [Category K] [Small.{w} K]
    (G : ringedSiteModuleCategory.{u, v, w, w} J O) :
    PreservesColimitsOfShape K (tensorLeft G) := sorry

/-- Tensoring module sheaves on the right preserves colimits of shapes with `w`-small object types. -/
@[stacks 03EP "right tensor preserves shaped colimits", instance]
theorem tensorRightPreservesColimitsOfShape
    {K : Type*} [Category K] [Small.{w} K]
    (G : ringedSiteModuleCategory.{u, v, w, w} J O) :
    PreservesColimitsOfShape K (tensorRight G) := sorry

/-- Tensoring module sheaves on the left preserves colimits whose object universe is at most `w`. -/
@[stacks 03EP "left tensor preserves sized colimits", instance]
theorem tensorLeftPreservesColimitsOfSize
    [UnivLE.{w', w}]
    (G : ringedSiteModuleCategory.{u, v, w, w} J O) :
    PreservesColimitsOfSize.{v', w'} (tensorLeft G) := sorry

/-- Tensoring module sheaves on the right preserves colimits whose object universe is at most `w`. -/
@[stacks 03EP "right tensor preserves sized colimits", instance]
theorem tensorRightPreservesColimitsOfSize
    [UnivLE.{w', w}]
    (G : ringedSiteModuleCategory.{u, v, w, w} J O) :
    PreservesColimitsOfSize.{v', w'} (tensorRight G) := sorry

/-- Tensoring module sheaves on the left preserves all colimits small in the section universe. -/
@[stacks 03EP "(2)"]
instance tensorLeftPreservesColimits
    (G : ringedSiteModuleCategory.{u, v, w, w} J O) :
    PreservesColimitsOfSize.{w, w} (tensorLeft G) := sorry

/-- Tensoring module sheaves on the right preserves all colimits small in the section universe. -/
@[stacks 03EP "right tensor preserves colimits"]
instance tensorRightPreservesColimits
    (G : ringedSiteModuleCategory.{u, v, w, w} J O) :
    PreservesColimitsOfSize.{w, w} (tensorRight G) := sorry

end SheafOfModules.RingedSite
