/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Underlying
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Zero
public import ReasLib.Topology.Sheaf.Flasque
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Flasque module sheaves

This file owns the module-sheaf object property obtained by forgetting the module structure to an
additive sheaf.  Godement resolutions and other replacement constructions consume this property;
the property is therefore kept independent of the Godement namespace.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open scoped AlgebraicGeometry ZeroObject

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.Modules

variable (X : RingedSpace.{u})

/-- A module sheaf is flasque when its underlying additive sheaf is flasque. -/
@[stacks 01EK "flasque module sheaves"]
def flasque : ObjectProperty X.Modules :=
  fun F => TopCat.Sheaf.IsFlasque ((moduleUnderlyingSheaf X).obj F)

/-- The full subcategory of flasque module sheaves. -/
@[stacks 01EK "flasque module-sheaf subcategory"]
abbrev Flasque := (flasque X).FullSubcategory

/-- Membership in the module-sheaf flasque property is exactly flasqueness of the underlying
additive sheaf. -/
@[stacks 01EK "underlying-sheaf characterization of flasqueness"]
theorem mem_flasque_iff (F : X.Modules) :
    flasque X F ↔ TopCat.Sheaf.IsFlasque ((moduleUnderlyingSheaf X).obj F) := Iff.rfl

/-- The zero module sheaf is flasque. -/
@[stacks 01EK "zero module sheaf is flasque"]
theorem flasque_zero : flasque X (0 : X.Modules) := sorry

/-- Flasqueness of module sheaves is invariant under isomorphism. -/
@[stacks 01EK "isomorphism closure of flasque module sheaves"]
theorem flasque_of_iso {F G : X.Modules} (e : F ≅ G) (hF : flasque X F) :
    flasque X G := sorry

/-- Finite coproducts of flasque module sheaves are flasque. -/
@[stacks 01EK "finite coproduct closure of flasque module sheaves"]
theorem flasque_coproduct {J : Type*} [Finite J] (F : J → X.Modules) [HasCoproduct F]
    (hF : ∀ j, flasque X (F j)) : flasque X (∐ F) := sorry

end AlgebraicGeometry.RingedSpace.Modules
