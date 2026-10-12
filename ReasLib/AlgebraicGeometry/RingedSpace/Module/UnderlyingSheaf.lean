/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sheaves.Abelian
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Grothendieck
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Definition

/-!
# Underlying additive sheaves of module sheaves

This module records the forgetful functors from module sheaves on a ringed
space to additive sheaves and presheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u w w'

namespace AlgebraicGeometry.RingedSpace

/-- The forgetful functor from `𝒪_X`-modules to sheaves of abelian groups. -/
abbrev moduleUnderlyingSheaf (X : RingedSpace.{u}) :
    X.Modules ⥤ X.carrier.Sheaf AddCommGrpCat.{u} :=
  SheafOfModules.toSheaf X.ringCatSheaf

/-- The underlying-additive-sheaf functor of `X.Modules` is additive. -/
theorem moduleUnderlyingSheaf_additive (X : RingedSpace.{u}) :
    (moduleUnderlyingSheaf X).Additive := sorry

/-- The underlying-additive-sheaf functor of `X.Modules` is faithful. -/
theorem moduleUnderlyingSheaf_faithful (X : RingedSpace.{u}) :
    (moduleUnderlyingSheaf X).Faithful := sorry

/-- The underlying-additive-sheaf functor of `X.Modules` preserves finite limits. -/
theorem moduleUnderlyingSheaf_preservesFiniteLimits (X : RingedSpace.{u}) :
    PreservesFiniteLimits (moduleUnderlyingSheaf X) := sorry

/-- The underlying-additive-sheaf functor of `X.Modules` preserves all small limits. -/
@[stacks 03DB "underlying module sheaf preserves limits"]
theorem moduleUnderlyingSheaf_preservesLimits (X : RingedSpace.{u}) :
    PreservesLimits (moduleUnderlyingSheaf X) := sorry

/-- The underlying-additive-sheaf functor preserves limits of every universe-polymorphic shape. -/
@[stacks 03DB "underlying module sheaf preserves limits of any shape"]
theorem moduleUnderlyingSheaf_preservesLimitsOfShape
    (X : RingedSpace.{u}) {J : Type w} [Category.{w'} J] :
    PreservesLimitsOfShape J (moduleUnderlyingSheaf X) := sorry

/-- The underlying-additive-sheaf functor of `X.Modules` preserves finite colimits. -/
theorem moduleUnderlyingSheaf_preservesFiniteColimits (X : RingedSpace.{u}) :
    PreservesFiniteColimits (moduleUnderlyingSheaf X) := sorry

/-- The forgetful functor from `𝒪_X`-modules to additive presheaves. -/
abbrev moduleUnderlyingPresheaf (X : RingedSpace.{u}) :
    X.Modules ⥤ X.carrier.Presheaf AddCommGrpCat.{u} :=
  moduleUnderlyingSheaf X ⋙
    sheafToPresheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}

/-- Forgetting an `𝒪_X`-module first to an additive sheaf and then to a
presheaf agrees with its canonical underlying presheaf of abelian groups. -/
noncomputable abbrev moduleUnderlyingPresheafIso (X : RingedSpace.{u}) :
    moduleUnderlyingPresheaf X ≅
      SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.toPresheaf X.ringCatSheaf.obj :=
  SheafOfModules.toSheafCompSheafToPresheafIso (R := X.ringCatSheaf)

/-- The underlying-additive-presheaf functor of `X.Modules` is additive. -/
theorem moduleUnderlyingPresheaf_additive (X : RingedSpace.{u}) :
    (moduleUnderlyingPresheaf X).Additive := sorry

end AlgebraicGeometry.RingedSpace
