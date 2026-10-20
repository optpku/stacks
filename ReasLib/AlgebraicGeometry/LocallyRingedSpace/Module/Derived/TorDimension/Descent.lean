module

public import ReasLib.Algebra.Homology.DerivedCategory.ScalarExtension.TorAmplitude
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Pullback
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.TorDimension.Stalk
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.FlatMorphism
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.LocallyRingedSpace.Hom

/-- Derived pullback along a surjective flat morphism of locally ringed spaces detects
Tor-amplitude in a fixed interval. -/
@[stacks 09UD]
theorem hasTorAmplitudeIn_iff_pullback_of_surjective_of_flat
    {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules X.toRingedSpace)]
    [DerivedCategory.DerivedTensor.Right.Has (C := RingedSpace.Modules Y.toRingedSpace)]
    [RingedSpace.Hom.IsFlat f.toShHom] (h_surjective : Function.Surjective f.base)
    (E : RingedSpace.ModuleDerived Y.toRingedSpace) (a b : ℤ) :
    RingedSpace.HasTorAmplitudeIn E a b ↔
      RingedSpace.HasTorAmplitudeIn
        ((RingedSpace.modulePullbackDerived f.toShHom).obj E) a b := sorry

end AlgebraicGeometry.LocallyRingedSpace.Hom
