/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.NaiveCotangent.TorAmplitude

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom.NaiveCotangent

/- Lemma 37.62.17: For a flat morphism `f : X ⟶ Y` of finite presentation, being a
local complete intersection, being syntomic, having its derived naive cotangent complex of
Tor-amplitude in `[-1, 0]`, and having that complex perfect with the same Tor-amplitude are
equivalent. -/
@[stacks 0FK3] #check
  (AlgebraicGeometry.Scheme.Hom.NaiveCotangent.flatFinitePresentation_tfae :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Scheme.Hom.FinitePresentation f],
      List.TFAE [LocallyOfType RingHom.IsLocalCompleteIntersection f,
        Syntomic f,
        RingedSpace.HasTorAmplitudeIn
          (DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom)) (-1) 0,
        RingedSpace.ModuleDerived.IsPerfect
            (DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom)) ∧
          RingedSpace.HasTorAmplitudeIn
            (DerivedCategory.Q.obj (RingedSpace.naiveCotangent f.toShHom)) (-1) 0])

end Scheme.Hom.NaiveCotangent
end AlgebraicGeometry
