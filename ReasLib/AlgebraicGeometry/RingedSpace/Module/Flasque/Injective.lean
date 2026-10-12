/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flasque
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Injective
public import ReasLib.Topology.Sheaf.Flasque
import Mathlib.Tactic.CrossRefAttribute

/-!
# Injective module sheaves are flasque

This leaf records the injective-to-flasque implication at the ringed-space module level.  The
object-property statement is the reusable owner; the underlying additive-sheaf theorem is a thin
bridge for consumers working in `TopCat.Sheaf AddCommGrpCat`.
-/

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Modules

variable {X : RingedSpace.{u}}

/-- 20.12.2 / 09SX: an injective module sheaf belongs to the flasque module-sheaf property. -/
@[stacks 09SX "injective module sheaves are flasque"]
theorem flasque_of_injective (ℐ : X.Modules) (hℐ : Injective ℐ) :
    flasque X ℐ := sorry

/-- 20.12.2 / 09SX: the underlying additive sheaf of an injective module sheaf is flasque. -/
@[stacks 09SX "underlying additive sheaf"]
theorem underlying_isFlasque_of_injective (ℐ : X.Modules) (hℐ : Injective ℐ) :
    TopCat.Sheaf.IsFlasque ((moduleUnderlyingSheaf X).obj ℐ) := sorry

/-- The canonical flasque instance on the underlying additive sheaf of an injective module
sheaf.  No auxiliary `Fact` wrapper is needed because `Injective ℐ` is already a typeclass. -/
@[stacks 09SX "injective underlying sheaf instance", instance]
theorem underlyingIsFlasque (ℐ : X.Modules) [Injective ℐ] :
    TopCat.Sheaf.IsFlasque ((moduleUnderlyingSheaf X).obj ℐ) := sorry

end AlgebraicGeometry.RingedSpace.Modules
