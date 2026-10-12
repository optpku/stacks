/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Duality
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}
variable [KFlat.HomotopyTensorDescends X] [KFlat.TensorDescends X]
variable [KFlat.IsLocalization X]
variable [MonoidalClosed (ModuleDerived X)]

/- Lemma 20.50.5 (1): the closed-monoidal dual of a perfect object of `D(𝒪_X)` is
perfect. -/
@[stacks 08DQ "(1)"]
#check @IsPerfect.dual

/- Lemma 20.50.5 (2): the canonical map from a perfect object to its bidual is an
isomorphism. -/
@[stacks 08DQ "(2)"]
#check fun {K : ModuleDerived X} (hK : IsPerfect K) ↦
  hK.isRightDualizable.isIso_bidualComparison

/- Lemma 20.50.5 (3): tensoring with the dual of a perfect object canonically represents
the internal Hom out of that object. -/
@[stacks 08DQ "(3)"]
#check fun {K : ModuleDerived X} (hK : IsPerfect K) (M : ModuleDerived X) ↦
  hK.isRightDualizable.isIso_tensorComparison M

/- Lemma 20.50.5 (4): the canonical map from morphisms out of the tensor unit into
`M ⊗ MonoidalClosed.dual K` to morphisms `K ⟶ M` is bijective. -/
@[stacks 08DQ "(4)"]
#check fun {K : ModuleDerived X} (hK : IsPerfect K) (M : ModuleDerived X) ↦
  hK.isRightDualizable.homComparison_bijective M

end AlgebraicGeometry.RingedSpace.ModuleDerived
