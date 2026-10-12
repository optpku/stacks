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

/- Lemma 20.42.8 (08I1): the degree-zero map from the dual comparison to a morphism is the
generic closed-monoidal `Dual.homComparison`. -/
@[stacks 08I1 "degree-zero dual comparison"]
#check @MonoidalClosed.Dual.homComparison

/- Typed ringed-space specialization of the source-facing map. -/
@[stacks 08I1]
#check fun (L M : ModuleDerived X) ↦ MonoidalClosed.Dual.homComparison L M

/- Its pointwise formula and target naturality are part of the reusable owner. -/
@[stacks 08I1 "pointwise degree-zero dual comparison"]
#check @MonoidalClosed.Dual.homComparison_apply
@[stacks 08I1 "naturality of the degree-zero dual comparison"]
#check @MonoidalClosed.Dual.homComparison_natural_apply

end AlgebraicGeometry.RingedSpace
