/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier
import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect

open AlgebraicGeometry

universe u

section

variable (X : Scheme.{u}) (D : X.IdealSheafData)
variable [IsEffectiveCartierDivisor D.subschemeι]
variable (M : RingedSpace.ModuleDerived X.toRingedSpace)
variable (hM : RingedSpace.ModuleDerived.IsPerfect M)

/- Situation 38.43.1: `X` is a scheme, `D.subscheme` is an effective Cartier divisor
with ideal sheaf `D.toSubobject ⊆ 𝒪_X`, and `M` is a perfect object of `D(𝒪_X)`. -/
@[stacks 0F8S] #check (AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect M : Prop)

#check D.toSubobject
#check (inferInstance : IsEffectiveCartierDivisor D.subschemeι)
#check M
#check (hM : AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect M)

end
