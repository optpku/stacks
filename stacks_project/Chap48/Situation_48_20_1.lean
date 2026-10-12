/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import Mathlib.AlgebraicGeometry.Noetherian
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Dualizing

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

section

variable (S : Scheme.{u}) [IsNoetherian S]
variable [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)]
variable (H : MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace))
variable (ωS : RingedSpace.ModuleDerived S.toRingedSpace)
variable (hωS : ωS.IsDualizingComplex H)

/- Situation 48.20.1: `S` is a Noetherian scheme and `ωS` is a dualizing complex on `S`. -/
@[stacks 0AU4] #check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.IsDualizingComplex
    (X := S.toRingedSpace) :
    ∀ (K : RingedSpace.ModuleDerived S.toRingedSpace)
      [MonoidalCategory (RingedSpace.ModuleDerived S.toRingedSpace)],
      MonoidalClosed (RingedSpace.ModuleDerived S.toRingedSpace) → Prop)

#check (hωS : ωS.IsDualizingComplex H)

end
