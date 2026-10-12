/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cohomology.Pushforward
public import ReasLib.Topology.Sheaf.Cohomology.Bridge
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomology of flasque module sheaves

This leaf keeps the ringed-space module specialization of flasque-sheaf acyclicity next to the
module-valued cohomology owners.  The underlying additive statement remains available through
`CategoryTheory.Sheaf.IsFlasque.isZero_cohomology`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleCohomology

variable {X : RingedSpace.{u}}
variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- Lemma 20.12.3 (09SY), module-valued form: a flasque module sheaf has zero positive-degree
cohomology over every open, retaining the `sectionsRingOnOpen`-module structure. -/
@[stacks 09SY "module-valued cohomology of a flasque sheaf"]
theorem isZero_module_of_flasque
    (ℱ : X.Modules)
    [TopCat.Sheaf.IsFlasque ((moduleUnderlyingSheaf X).obj ℱ)]
    (U : Opens X.carrier) {p : ℕ} (hp : 0 < p) :
    IsZero (moduleCohomologyAtOpen U ℱ p) := sorry

/-- Source-facing bridge from explicit underlying-sheaf flasqueness to the module-valued result. -/
@[stacks 09SY "explicit module flasque-cohomology bridge"]
theorem isZero_module_of_flasque'
    (ℱ : X.Modules)
    (hℱ : TopCat.Sheaf.IsFlasque ((moduleUnderlyingSheaf X).obj ℱ))
    (U : Opens X.carrier) (p : ℕ) (hp : 0 < p) :
    IsZero (moduleCohomologyAtOpen U ℱ p) := sorry


end AlgebraicGeometry.RingedSpace.ModuleCohomology

end
