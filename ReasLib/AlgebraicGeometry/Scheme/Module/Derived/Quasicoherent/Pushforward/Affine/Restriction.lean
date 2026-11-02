/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.Affine.BoundedBelow

/-!
# Bounded-below restriction from a pushed-forward structure sheaf
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.ObjectProperty
open DerivedCategory.TStructure
open DerivedCategory.Plus
open RingedSpace.Hom.PushforwardStructure

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

variable {X Y : Scheme.{u}}

/-- The ambient derived restriction of scalars along `𝒪_X ⟶ f_*𝒪_Y`, on bounded-below
objects with quasi-coherent cohomology over `f_*𝒪_Y`. -/
noncomputable abbrev pushforwardRestrictionPlusAmbient (f : Y ⟶ X) :
    PushforwardQCohPlus f ⥤ RingedSpace.ModuleDerived X.toRingedSpace :=
  CohomologyIn.ambient
      (RingedSpace.quasiCoherentModuleProperty (target f.toShHom)) ⋙
    pushforwardQCohRestrictionDerived f

/-- Derived restriction of scalars along `𝒪_X ⟶ f_*𝒪_Y` preserves the bounded-below
condition. -/
theorem pushforwardRestrictionPlusAmbient_boundedBelow (f : Y ⟶ X) :
    ∀ K : PushforwardQCohPlus f,
      (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace))
        ((pushforwardRestrictionPlusAmbient f).obj K) := sorry

/-- The bounded-below lift of derived restriction of scalars along
`𝒪_X ⟶ f_*𝒪_Y`. -/
noncomputable def pushforwardRestrictionToPlus (f : Y ⟶ X) :
    PushforwardQCohPlus f ⥤ DerivedCategory.Plus X.toRingedSpace.Modules :=
  (t.plus : ObjectProperty (RingedSpace.ModuleDerived X.toRingedSpace)).lift
    (pushforwardRestrictionPlusAmbient f)
    (pushforwardRestrictionPlusAmbient_boundedBelow f)

/-- Bounded-below derived restriction of scalars along `𝒪_X ⟶ f_*𝒪_Y` preserves
quasi-coherent cohomology for a quasi-compact, quasi-separated morphism. -/
theorem pushforwardRestrictionToPlus_quasicoherent (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] :
    ∀ K : PushforwardQCohPlus f,
      cohomologyIn
        (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)
        ((pushforwardRestrictionToPlus f).obj K) := by
  intro K
  exact pushforwardQCohRestrictionDerived.mapsTo f _ K.property

/-- Bounded-below derived restriction of scalars along `𝒪_X ⟶ f_*𝒪_Y`, restricted to
objects with quasi-coherent cohomology for a quasi-compact, quasi-separated morphism. -/
noncomputable def pushforwardRestrictionPlus (f : Y ⟶ X)
    [QuasiCompact f] [QuasiSeparated f] :
    PushforwardQCohPlus f ⥤ Plus X :=
  (cohomologyIn
      (RingedSpace.quasiCoherentModuleProperty X.toRingedSpace)).lift
    (pushforwardRestrictionToPlus f)
    (pushforwardRestrictionToPlus_quasicoherent f)

end AlgebraicGeometry.Scheme.DerivedQCoh
