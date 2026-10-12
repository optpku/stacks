/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Tensor
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Tor-amplitude on ringed spaces

The generic Tor-amplitude API for the canonical tensor product on `Modules X` specializes to
derived modules and degree-zero module sheaves on a ringed space.
-/

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open scoped CategoryTheory.DerivedCategory.DerivedTensor

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

/-- The object property of having lower Tor-amplitude at least `a` on a ringed space. -/
abbrev torAmplitudeGE (a : ℤ) : ObjectProperty (ModuleDerived X) :=
  @DerivedCategory.DerivedTensor.torAmplitudeGE (Modules X) _ _ _ _ _
    (SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor X.sheaf)
    (SheafOfModules.RingedSite.moduleCategoryHasDerivedTensor X.sheaf).right a

/-- A derived `𝒪_X`-module has lower Tor-amplitude at least `a`. -/
abbrev HasTorAmplitudeGE (E : ModuleDerived X) (a : ℤ) : Prop :=
  torAmplitudeGE (X := X) a E

/-- The object property of having upper Tor-amplitude at most `b` on a ringed space. -/
abbrev torAmplitudeLE (b : ℤ) : ObjectProperty (ModuleDerived X) :=
  @DerivedCategory.DerivedTensor.torAmplitudeLE (Modules X) _ _ _ _ _
    (SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor X.sheaf)
    (SheafOfModules.RingedSite.moduleCategoryHasDerivedTensor X.sheaf).right b

/-- A derived `𝒪_X`-module has upper Tor-amplitude at most `b`. -/
abbrev HasTorAmplitudeLE (E : ModuleDerived X) (b : ℤ) : Prop :=
  torAmplitudeLE (X := X) b E

/-- The object property of derived `𝒪_X`-modules with Tor-amplitude in `[a, b]`. -/
@[stacks 08CG "(1) object property"]
abbrev torAmplitudeIn (a b : ℤ) : ObjectProperty (ModuleDerived X) :=
  @DerivedCategory.DerivedTensor.torAmplitudeIn (Modules X) _ _ _ _ _
    (SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor X.sheaf)
    (SheafOfModules.RingedSite.moduleCategoryHasDerivedTensor X.sheaf).right a b

/-- A derived `𝒪_X`-module has Tor-amplitude in `[a, b]` when its canonical derived tensor
product with every degree-zero module sheaf has homology only in that interval. -/
@[stacks 08CG "(1)"]
abbrev HasTorAmplitudeIn (E : ModuleDerived X) (a b : ℤ) : Prop :=
  torAmplitudeIn (X := X) a b E

/-- Tor-amplitude in `[a, b]` is equivalently the conjunction of its lower and upper bounds. -/
theorem hasTorAmplitudeIn_iff (E : ModuleDerived X) (a b : ℤ) :
    HasTorAmplitudeIn E a b ↔ HasTorAmplitudeGE E a ∧ HasTorAmplitudeLE E b := sorry

/-- Tor-amplitude on a ringed space unfolds to homology vanishing outside the interval after
canonical derived tensoring with every degree-zero module sheaf. -/
theorem hasTorAmplitudeIn_iff_homology (E : ModuleDerived X) (a b : ℤ) :
    HasTorAmplitudeIn E a b ↔
      ∀ (F : Modules X) (i : ℤ), i ∉ Set.Icc a b →
        IsZero ((DerivedCategory.homologyFunctor (Modules X) i).obj
          (@DerivedCategory.DerivedTensor.Right.obj (Modules X) _ _ _ _ _
            (SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor X.sheaf)
            E ((DerivedCategory.singleFunctor (Modules X) 0).obj F)
            (SheafOfModules.RingedSite.moduleCategoryHasDerivedTensor X.sheaf).right)) := sorry

/-- The object property of derived `𝒪_X`-modules of finite Tor dimension. -/
@[stacks 08CG "(2) object property"]
abbrev finiteTorDimension : ObjectProperty (ModuleDerived X) :=
  @DerivedCategory.DerivedTensor.finiteTorDimension (Modules X) _ _ _ _ _
    (SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor X.sheaf)
    (SheafOfModules.RingedSite.moduleCategoryHasDerivedTensor X.sheaf).right

/-- A derived `𝒪_X`-module has finite Tor dimension when it has Tor-amplitude in some finite
interval. -/
@[stacks 08CG "(2)"]
abbrev HasFiniteTorDimension (E : ModuleDerived X) : Prop :=
  finiteTorDimension (X := X) E

/-- Finite Tor dimension is equivalent to the existence of a finite Tor-amplitude interval. -/
theorem hasFiniteTorDimension_iff (E : ModuleDerived X) :
    HasFiniteTorDimension E ↔ ∃ a b : ℤ, HasTorAmplitudeIn E a b := sorry

/-- A fixed finite Tor-amplitude interval gives finite Tor dimension. -/
theorem HasTorAmplitudeIn.hasFiniteTorDimension
    {E : ModuleDerived X} {a b : ℤ} (hE : HasTorAmplitudeIn E a b) :
    HasFiniteTorDimension E := sorry

/-- A Tor-amplitude interval supplies its lower bound. -/
theorem HasTorAmplitudeIn.hasTorAmplitudeGE
    {E : ModuleDerived X} {a b : ℤ} (hE : HasTorAmplitudeIn E a b) :
    HasTorAmplitudeGE E a := sorry

/-- A Tor-amplitude interval supplies its upper bound. -/
theorem HasTorAmplitudeIn.hasTorAmplitudeLE
    {E : ModuleDerived X} {a b : ℤ} (hE : HasTorAmplitudeIn E a b) :
    HasTorAmplitudeLE E b := sorry

/-- The object property of `𝒪_X`-modules with Tor dimension at most `d`. -/
@[stacks 08CG "(4), object property"]
abbrev moduleTorDimensionLE (d : ℕ) : ObjectProperty (Modules X) :=
  @DerivedCategory.DerivedTensor.torDimensionLE (Modules X) _ _ _ _ _
    (SheafOfModules.RingedSite.moduleCategoryHasMapBifunctor X.sheaf)
    (SheafOfModules.RingedSite.moduleCategoryHasDerivedTensor X.sheaf).right d

/-- An `𝒪_X`-module has Tor dimension at most `d` when its degree-zero derived object has
Tor-amplitude in `[-d, 0]`. -/
@[stacks 08CG "(4)"]
abbrev ModuleHasTorDimensionLE (F : Modules X) (d : ℕ) : Prop :=
  moduleTorDimensionLE (X := X) d F

/-- The module Tor-dimension bound is the corresponding Tor-amplitude bound on its degree-zero
derived object. -/
theorem moduleHasTorDimensionLE_iff (F : Modules X) (d : ℕ) :
    ModuleHasTorDimensionLE F d ↔
      HasTorAmplitudeIn
        ((DerivedCategory.singleFunctor (Modules X) 0).obj F) (-(d : ℤ)) 0 := sorry

end AlgebraicGeometry.RingedSpace
