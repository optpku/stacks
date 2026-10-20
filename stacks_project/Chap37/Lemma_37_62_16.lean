module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.TorAmplitude
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.62.16: for a perfect morphism `f : X ⟶ Y` of locally Noetherian
schemes, being a local complete intersection, having `NL[f.toShHom]` of Tor-amplitude in
`[-1, 0]`, and having it perfect with that Tor-amplitude are equivalent. -/
@[stacks 0FK2]
#check (AlgebraicGeometry.Scheme.Hom.NaiveCotangent.perfect_tfae :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [DerivedCategory.DerivedTensor.Right.Has (C := AlgebraicGeometry.RingedSpace.Modules X.toRingedSpace)]
    [AlgebraicGeometry.IsLocallyNoetherian X] [AlgebraicGeometry.IsLocallyNoetherian Y]
    [AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap f],
    List.TFAE [AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection f,
      AlgebraicGeometry.RingedSpace.HasTorAmplitudeIn
        (DerivedCategory.Q.obj (AlgebraicGeometry.RingedSpace.naiveCotangent f.toShHom))
          (-1) 0,
      AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect
          (DerivedCategory.Q.obj (AlgebraicGeometry.RingedSpace.naiveCotangent f.toShHom)) ∧
        AlgebraicGeometry.RingedSpace.HasTorAmplitudeIn
          (DerivedCategory.Q.obj (AlgebraicGeometry.RingedSpace.naiveCotangent f.toShHom))
            (-1) 0])
