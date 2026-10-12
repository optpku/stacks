/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.PicardGroup.Invertible
import StacksCheckRecall

@[expose] public section

/-!
# Definition 15.118.1

The two source clauses are canonical recalls: tensor-invertibility is
`CategoryTheory.MonoidalCategory.isInvertibleObject`, and triviality is
`CategoryTheory.MonoidalCategory.isUnitObject`. The module-specific bridges and the reusable
invertible-module subcategory are owned by `ReasLib.RingTheory.PicardGroup.Invertible`.

@stack 0B8H
-/

open CategoryTheory MonoidalCategory

universe u

namespace ModuleCat

variable {R : Type u} [CommRing R]
variable (M : ModuleCat R)

/- Definition 15.118.1 (1): tensoring on the left by `M` is an equivalence. -/
@[stacks 0B8H "Definition 15.118.1 (1): an invertible module"]
#check isInvertibleObject M

/- Definition 15.118.1 (2): an invertible module is trivial when it is isomorphic to the unit. -/
@[stacks 0B8H "Definition 15.118.1 (2): a trivial invertible module"]
#check isUnitObject M

#check @ModuleCat.isInvertibleObject_iff_invertible
#check @ModuleCat.isUnitObject_iff_linearEquiv
#check @ModuleCat.Invertible
#check @ModuleCat.Invertible.Core

end ModuleCat

end
