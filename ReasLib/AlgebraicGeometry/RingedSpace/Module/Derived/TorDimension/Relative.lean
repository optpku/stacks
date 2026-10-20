/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.RelativeRestriction
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X S : RingedSpace.{u}}

/-- The object property of having Tor-amplitude in `[a, b]` after restriction from
`𝒪_X` to the inverse-image sheaf `f⁻¹𝒪_S`. -/
noncomputable def torAmplitudeInOver (f : X ⟶ S)
    [DerivedCategory.DerivedTensor.Right.Has
      (C := Modules (RingedSpace.Hom.inverseImageBase f))] (a b : ℤ) :
    ObjectProperty (ModuleDerived X) :=
  (RingedSpace.torAmplitudeIn a b).inverseImage (relativeRestriction f)

/-- A derived `𝒪_X`-module has Tor-amplitude in `[a, b]` over `S` when its restriction to
`f⁻¹𝒪_S` has that Tor-amplitude. -/
abbrev HasTorAmplitudeInOver (f : X ⟶ S)
    [DerivedCategory.DerivedTensor.Right.Has
      (C := Modules (RingedSpace.Hom.inverseImageBase f))] (E : ModuleDerived X) (a b : ℤ) : Prop :=
  torAmplitudeInOver f a b E

/-- Relative Tor-amplitude is the ordinary Tor-amplitude of the derived restriction to
`f⁻¹𝒪_S`. -/
theorem hasTorAmplitudeInOver_iff (f : X ⟶ S)
    [DerivedCategory.DerivedTensor.Right.Has
      (C := Modules (RingedSpace.Hom.inverseImageBase f))] (E : ModuleDerived X) (a b : ℤ) :
    HasTorAmplitudeInOver f E a b ↔
      RingedSpace.HasTorAmplitudeIn ((relativeRestriction f).obj E) a b := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived
