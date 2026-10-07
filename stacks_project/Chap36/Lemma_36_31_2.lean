module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.FiberEulerCharacteristic

@[expose] public section

open AlgebraicGeometry

universe u

/- Lemma 36.31.2: for a perfect derived module on a scheme, the Euler characteristic
of its derived residue-field fiber is locally constant. -/
@[stacks 0BDJ] #check
  (AlgebraicGeometry.Scheme.ModuleDerived.fiberEulerChar_isLocallyConstant :
    ∀ {X : Scheme.{u}} (E : RingedSpace.ModuleDerived X.toRingedSpace),
      RingedSpace.ModuleDerived.IsPerfect E →
        IsLocallyConstant (AlgebraicGeometry.Scheme.ModuleDerived.fiberEulerChar E))
