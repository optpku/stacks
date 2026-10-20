/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings.Exact
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Basic
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Monoidal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RingedSite.CommRingHom
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude
public import ReasLib.CategoryTheory.Monoidal.Flat

/-! # Relative coefficients and Tor-amplitude for algebraic spaces

Scalar restriction to the inverse-image structure sheaf defines intrinsic relative
flatness and Tor-amplitude on the small étale site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.MonoidalCategory ComplexShape
open SheafOfModules.RingedSite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace Modules

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Module sheaves over the inverse-image coefficient sheaf `f⁻¹𝒪_Y` on `X_étale`. -/
abbrev Relative (f : X ⟶ Y) :=
  ringedSiteModuleCategory.{u + 1, u, u, u}
    (smallEtaleTopology X) (commInverseImageStructureSheaf f)

/-- The standard derived category structure for inverse-image coefficient modules. -/
instance relativeHasDerivedCategory (f : X ⟶ Y) : HasDerivedCategory (Relative f) :=
  HasDerivedCategory.standard (Relative f)

/-- Native module-sheaf coproducts totalize the tensor product of unbounded complexes. -/
instance relativeHasMapBifunctor (f : X ⟶ Y)
    (K L : CochainComplex (Relative f) ℤ) :
    HomologicalComplex.HasMapBifunctor K L (curriedTensor (Relative f)) (up ℤ) := by
  intro n
  infer_instance

/-- Unbounded fixed-right derived tensor products exist over inverse-image coefficients. -/
instance relativeHasDerivedTensorRight (f : X ⟶ Y) :
    DerivedCategory.DerivedTensor.Right.Has (C := Relative f) :=
  sorry

/-- Restriction of module scalars along the inverse-image structure map `f⁻¹𝒪_Y ⟶ 𝒪_X`. -/
@[reducible]
def relativeRestriction (f : X ⟶ Y) : Modules X ⥤ Relative f :=
  SheafOfModules.restrictScalars
    (ringSheafMap.{u + 1, u, u} (commInverseImageStructureSheafMap f) ≫
      (commRingSheafIso X).hom)

/-- A module is flat over the base when its restriction to inverse-image coefficients is flat. -/
def IsFlatOver (M : Modules X) (f : X ⟶ Y) : Prop :=
  IsFlat ((relativeRestriction f).obj M)

end Modules

namespace ModuleDerived

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- Exact scalar restriction on unbounded derived modules to `f⁻¹𝒪_Y` coefficients. -/
def restrictToRelativeCoefficients (f : X ⟶ Y) :
    ModuleDerived X ⥤ DerivedCategory (Modules.Relative f) :=
  (Modules.relativeRestriction f).mapDerivedCategory

/-- Relative Tor-amplitude is Tor-amplitude after restriction to `f⁻¹𝒪_Y` coefficients. -/
def HasTorAmplitudeInOver (f : X ⟶ Y) (E : ModuleDerived X) (a b : ℤ) : Prop :=
  DerivedCategory.DerivedTensor.HasTorAmplitudeIn
    ((restrictToRelativeCoefficients f).obj E) a b

/-- Relative Tor-amplitude unfolds to Tor-amplitude over inverse-image coefficients. -/
theorem hasTorAmplitudeInOver_iff (f : X ⟶ Y) (E : ModuleDerived X) (a b : ℤ) :
    HasTorAmplitudeInOver f E a b ↔
      DerivedCategory.DerivedTensor.HasTorAmplitudeIn
        ((restrictToRelativeCoefficients f).obj E) a b :=
  Iff.rfl

/-- A module is flat over the base exactly when its degree-zero complex has relative
Tor-amplitude in `[0, 0]`. -/
theorem hasTorAmplitudeInOver_single_iff_isFlatOver (f : X ⟶ Y) (M : Modules X) :
    Modules.IsFlatOver M f ↔
      HasTorAmplitudeInOver f ((DerivedCategory.singleFunctor (Modules X) 0).obj M) 0 0 :=
  sorry

end ModuleDerived

end AlgebraicGeometry.AlgebraicSpace
