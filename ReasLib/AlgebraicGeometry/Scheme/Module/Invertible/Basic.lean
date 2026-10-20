/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Invertible
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Invertible
public import ReasLib.AlgebraicGeometry.Scheme.Module.Monoidal
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Basic invertible scheme modules

This leaf specializes the standard tensor-invertible-object property to the
canonical monoidal category of modules on a scheme.  Generic monoidal
mathematics continues to use `MonoidalCategory.isInvertibleObject` directly;
scheme-facing clients never choose a second tensor structure.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- An invertible scheme module is the standard tensor-invertible-object property in its
canonical module tensor category. -/
@[stacks 0FFN "invertible scheme module"]
abbrev Invertible (L : X.Modules) : Prop :=
  @MonoidalCategory.isInvertibleObject X.Modules
    AlgebraicGeometry.Scheme.Modules.instCategory
    (AlgebraicGeometry.Scheme.Modules.instMonoidalCategory X) L

namespace Invertible

/-- An invertibility witness supplies equivalence of tensoring on the right. -/
@[stacks 0FFN "tensoring by an invertible scheme module is an equivalence"]
theorem tensorRight_isEquivalence {L : X.Modules} (hL : Invertible L) :
    Functor.IsEquivalence (tensorRight L) :=
  MonoidalCategory.isInvertibleObject.iff_tensorRight L |>.mp hL

/-- Package an available tensor-right equivalence as an invertibility witness.

This is a theorem rather than a reverse global instance, keeping typeclass search acyclic. -/
@[stacks 0FFN "invertibility from tensoring equivalence"]
theorem ofTensorRightIsEquivalence (L : X.Modules)
    (h : Functor.IsEquivalence (tensorRight L)) : Invertible L :=
  MonoidalCategory.isInvertibleObject.ofTensorRight L h

/-- The structure module is invertible for the chosen monoidal structure on scheme modules. -/
@[stacks 0FFN "tensor unit is invertible"]
instance unit_invertible :
    Invertible (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  MonoidalCategory.isInvertibleObject.of_iso
    (C := X.Modules)
    (SheafOfModules.RingedSite.unitIsoTensorUnit
      (J := Opens.grothendieckTopology X.toTopCat) (𝒪 := X.𝒪)).symm
    MonoidalCategory.isInvertibleObject.unit

/-- Replacing one member of a pointwise invertible family by an invertible module preserves
pointwise invertibility. -/
@[stacks 0FFN "updating an invertible family"]
instance update
    {ι : Type v} [DecidableEq ι] (L : ι → X.Modules) [∀ j : ι, Invertible (L j)]
    (i : ι) (M : X.Modules) [Invertible M] :
    ∀ j : ι, Invertible (Function.update L i M j) := sorry

end Invertible

/-- Tensor-invertibility of a scheme module in the canonical module category of the underlying
ringed space.  This bridge names the dependent instance boundary created by Mathlib's distinct
`Scheme.Modules` category presentation. -/
@[stacks 0FFN "ringed-space presentation of scheme-module invertibility"]
abbrev RingedSpaceIsInvertible (L : X.Modules) : Prop :=
  @MonoidalCategory.isInvertibleObject
    (RingedSpace.Modules X.toRingedSpace)
    SheafOfModules.instCategory
    (RingedSpace.modulesMonoidalCategory X.toRingedSpace) L

namespace Invertible

/-- Canonical Scheme-module invertibility transports to the underlying ringed-space
presentation. -/
@[stacks 0FFN "transport scheme-module invertibility to ringed spaces"]
theorem ringedSpaceIsInvertible {L : X.Modules}
    (hL : Invertible L) :
    RingedSpaceIsInvertible L := hL

/-- Canonical Scheme-module invertibility is automatically available to ringed-space APIs. -/
@[stacks 0FFN "ringed-space invertibility instance"]
instance instRingedSpaceIsInvertible {L : X.Modules}
    [hL : Invertible L] :
    @MonoidalCategory.isInvertibleObject
      (RingedSpace.Modules X.toRingedSpace)
      SheafOfModules.instCategory
      (RingedSpace.modulesMonoidalCategory X.toRingedSpace) L :=
  ringedSpaceIsInvertible hL

/-- An invertible scheme module is canonically quasicoherent. -/
instance instIsQuasicoherent (L : X.Modules) [Invertible L] :
    L.IsQuasicoherent := by
  infer_instance

end Invertible

end AlgebraicGeometry.Scheme.Modules
