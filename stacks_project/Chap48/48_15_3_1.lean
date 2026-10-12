/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.IdealSubobject.SecondOrder

universe u

/- 48.15.3.1: the canonical sequence
`0 ⟶ I / I ^ 2 ⟶ 𝒪_Y / I ^ 2 ⟶ 𝒪_X ⟶ 0`, where `𝒪_X = 𝒪_Y / I`, is exact. -/
@[stacks 0BQX] #check
  (AlgebraicGeometry.RingedSpace.secondOrderThickeningRow_shortExact :
    ∀ {Y : AlgebraicGeometry.RingedSpace.{u}}
      (I : AlgebraicGeometry.RingedSpace.IdealSubobject Y),
      (AlgebraicGeometry.RingedSpace.secondOrderThickeningRow I).ShortExact)
