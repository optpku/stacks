/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.TorAmplitude
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.62.15: if `f : X ⟶ Y` is a local complete-intersection morphism, then
its derived naive cotangent complex is perfect and has Tor-amplitude in `[-1, 0]`. -/
@[stacks 0FV6] #check
  (AlgebraicGeometry.Scheme.Hom.NaiveCotangent.isPerfect_and_hasTorAmplitudeIn_of_lci :
    ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
      [AlgebraicGeometry.LocallyOfType RingHom.IsLocalCompleteIntersection f],
      AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect
          (DerivedCategory.Q.obj
            (AlgebraicGeometry.RingedSpace.naiveCotangent f.toShHom)) ∧
        AlgebraicGeometry.RingedSpace.HasTorAmplitudeIn
          (DerivedCategory.Q.obj
            (AlgebraicGeometry.RingedSpace.naiveCotangent f.toShHom)) (-1) 0)
