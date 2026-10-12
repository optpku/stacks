/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Basic
public import ReasLib.CategoryTheory.Monoidal.Closed.Duality
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (ModuleDerived X)]
variable [BraidedCategory (ModuleDerived X)]
variable [MonoidalClosed (ModuleDerived X)]

/- Equation 20.42.8.1 (08I2): the canonical tensor/internal-Hom comparison is the generic
closed-monoidal map `M ⊗ dual L ⟶ (ihom L).obj M`. -/
@[stacks 08I2 "tensor/internal-Hom comparison"]
#check @MonoidalClosed.Dual.tensorComparison

/- The comparison is natural in both the target and the object being dualized. -/
@[stacks 08I2 "target naturality of the tensor/internal-Hom comparison"]
#check @MonoidalClosed.Dual.tensorComparison_natural
@[stacks 08I2 "source naturality of the tensor/internal-Hom comparison"]
#check @MonoidalClosed.Dual.tensorComparison_natural_source

/- Equation 20.42.8.1, specialized to `D(𝒪_X)`: -/
@[stacks 08I2]
#check fun (L M : ModuleDerived X) ↦ MonoidalClosed.Dual.tensorComparison L M

/- The associated dual evaluation is likewise owned by the generic closed-monoidal API. -/
@[stacks 08I2 "closed-monoidal dual evaluation"]
#check @MonoidalClosed.Dual.evaluation

#print axioms MonoidalClosed.Dual.tensorComparison
#print axioms MonoidalClosed.Dual.evaluation

end AlgebraicGeometry.RingedSpace
