module

public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.Module.Derived.TorDimension.Descent
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 36.12.1: derived pullback along a surjective flat morphism of locally ringed spaces
detects Tor-amplitude in a fixed interval. -/
@[stacks 09UD]
#check
  (AlgebraicGeometry.LocallyRingedSpace.Hom.hasTorAmplitudeIn_iff_pullback_of_surjective_of_flat :
    ∀ {X Y : AlgebraicGeometry.LocallyRingedSpace.{u}} (f : X ⟶ Y)
      [DerivedCategory.DerivedTensor.Right.Has
        (C := AlgebraicGeometry.RingedSpace.Modules X.toRingedSpace)]
      [DerivedCategory.DerivedTensor.Right.Has
        (C := AlgebraicGeometry.RingedSpace.Modules Y.toRingedSpace)]
      [RingedSpace.Hom.IsFlat f.toShHom],
      Function.Surjective f.base →
        ∀ (E : AlgebraicGeometry.RingedSpace.ModuleDerived Y.toRingedSpace) (a b : ℤ),
          AlgebraicGeometry.RingedSpace.HasTorAmplitudeIn E a b ↔
            AlgebraicGeometry.RingedSpace.HasTorAmplitudeIn
              ((AlgebraicGeometry.RingedSpace.modulePullbackDerived f.toShHom).obj E) a b)
