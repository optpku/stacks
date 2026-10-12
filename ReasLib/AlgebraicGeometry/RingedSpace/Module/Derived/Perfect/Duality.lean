/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Perfect.Dualizable
public import ReasLib.CategoryTheory.Monoidal.Closed.Dualizable
import Mathlib.Tactic.CrossRefAttribute

/-!
# Closed-monoidal duals of perfect complexes

This leaf contains consequences that require a chosen closed structure.  The characterization
of perfect objects by right dualizability lives in `Perfect.Dualizable`, so downstream users do
not acquire an internal-Hom assumption merely to use the tensor-duality API.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleDerived

variable {X : RingedSpace.{u}}
variable [KFlat.HomotopyTensorDescends X] [KFlat.TensorDescends X]
variable [KFlat.IsLocalization X]

/-- For any closed structure on the canonical derived tensor product, the closed-monoidal
dual of a perfect derived `𝒪_X`-module is perfect. -/
@[stacks 08DQ "dual perfectness"]
theorem IsPerfect.dual
    [MonoidalClosed (ModuleDerived X)]
    {K : ModuleDerived X} (hK : IsPerfect K) :
    IsPerfect (MonoidalClosed.dual K) := sorry

end AlgebraicGeometry.RingedSpace.ModuleDerived
