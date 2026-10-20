module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Basic
public import ReasLib.CategoryTheory.DerivedCategory.Monoidal.TorAmplitude

/-! # Tor-amplitude and lower bounds under derived pullback

A Tor-amplitude interval bounds the cohomology of every derived pullback from below.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ModuleDerived

variable {S : Scheme.{u}}

/-- A derived étale `𝒪_X`-module has Tor-amplitude in `[a, b]` when tensoring it with
any degree-zero étale `𝒪_X`-module has homology only in that interval. -/
abbrev HasTorAmplitudeIn {X : AlgebraicSpace S}
    [DerivedCategory.DerivedTensor.Right.Has (C := X.Modules)]
    (E : ModuleDerived X) (a b : ℤ) : Prop :=
  DerivedCategory.DerivedTensor.HasTorAmplitudeIn (C := X.Modules) E a b

/-- Derived pullback of a module with Tor-amplitude in `[a, b]` has cohomology only
in degrees at least `a`. -/
theorem pullback_isGE_of_hasTorAmplitudeIn {X Y : AlgebraicSpace S}
    [DerivedCategory.DerivedTensor.Right.Has (C := X.Modules)]
    (E : ModuleDerived X) (a b : ℤ) (hTor : HasTorAmplitudeIn E a b) (f : Y ⟶ X) :
    ((pullback f).obj E).IsGE a := sorry

end AlgebraicGeometry.AlgebraicSpace.ModuleDerived
