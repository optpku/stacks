/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Duality
public import ReasLib.CategoryTheory.Monoidal.Closed.Duality
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (ModuleDerived X)]
variable [BraidedCategory (ModuleDerived X)]
variable [MonoidalClosed (ModuleDerived X)]

/- Lemma 20.51.2 is the closed-monoidal dual-evaluation square
`MonoidalClosed.Dual.Pairing.commSq`, specialized to `D(𝒪_X)`.  The source assumes that `E` is
perfect because Lemma 20.50.5 then identifies the left edge with a bijection; the commutativity
itself holds at the more general closed-monoidal level. -/
@[stacks 0FVB]
#check fun (K E : ModuleDerived X) (_ : ModuleDerived.IsPerfect E) ↦
  MonoidalClosed.Dual.Pairing.commSq K E

/- The pointwise form states that cup product followed by dual evaluation equals evaluation of
the morphism produced by `MonoidalClosed.Dual.homComparison`. -/
#check @MonoidalClosed.Dual.Pairing.commSq_apply

end AlgebraicGeometry.RingedSpace
