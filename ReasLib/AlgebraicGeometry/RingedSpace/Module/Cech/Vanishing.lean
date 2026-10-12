/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Cech
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Flasque
public import ReasLib.CategoryTheory.Sites.Cech.Cofinal
public import ReasLib.Topology.Sheaf.Cohomology.Cech
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Vanishing of module-valued Čech cohomology

This leaf owns the module-sheaf bridge from flasqueness to positive-degree Čech vanishing.  The
underlying additive sheaf and the generic topological Čech theorem are imported directly, so the
owner is independent of the numbered Chapter 20 files.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

namespace ModuleCech

variable {ι : Type u}

/-- An `𝒪_X`-module is Čech-acyclic when its positive-degree Čech cohomology vanishes for every
indexed family of opens.  Each family is canonically a covering of its union. -/
@[stacks 01EV "Cech-acyclic module sheaves"]
def IsAcyclic (ℱ : X.Modules) : Prop :=
  ∀ {ι : Type u} (𝒰 : ι → Opens X.carrier) (p : ℕ),
    0 < p → IsZero (moduleCechCohomology 𝒰 ℱ p)

namespace IsAcyclic

/-- Čech-acyclicity on opens gives positive-degree vanishing for every family in a slice
`Over U`. -/
@[stacks 01EV "slice-Cech bridge for acyclic modules"]
theorem isZero_over
    {ℱ : X.Modules} {U : Opens X.carrier} {ι : Type u}
    (hℱ : IsAcyclic ℱ) (V : ι → Over U) (p : ℕ) (hp : 0 < p) :
    IsZero (cechCohomology U V ((moduleUnderlyingPresheaf X).obj ℱ) p) := sorry

/-- Lemma 20.11.8 (01EV): a module sheaf that is Čech-acyclic for every indexed open family has
zero positive-degree sheaf cohomology on every open. -/
@[stacks 01EV "cohomology vanishing for Cech-acyclic modules"]
theorem isZero_cohomology
    [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]
    {ℱ : X.Modules} (hℱ : IsAcyclic ℱ) (U : Opens X.carrier)
    {p : ℕ} (hp : 0 < p) :
    IsZero (((moduleUnderlyingSheaf X).obj ℱ).H' p U) := sorry

/-- Module-valued companion of the 01EV vanishing theorem.  The additive statement above remains
the bridge for generic sheaf-cohomology APIs, while this form preserves the section-ring action. -/
@[stacks 01EV "module-valued cohomology vanishing for Cech-acyclic modules"]
theorem isZero_module_cohomology
    {ℱ : X.Modules} (hℱ : IsAcyclic ℱ) (U : Opens X.carrier)
    {p : ℕ} (hp : 0 < p) :
    IsZero (moduleCohomologyAtOpen U ℱ p) := sorry

end IsAcyclic

/-- A flasque module has zero positive-degree Čech cohomology for every indexed open family. -/
@[stacks 09SZ "flasque modules have vanishing positive-degree Cech cohomology"]
theorem isZero_of_flasque
    (ℱ : X.Modules) (hℱ : Modules.flasque X ℱ)
    (𝒰 : ι → Opens X.carrier) (p : ℕ) (hp : 0 < p) :
    IsZero (moduleCechCohomology 𝒰 ℱ p) := sorry

/-- A flasque module sheaf is Čech-acyclic. -/
@[stacks 09SZ "flasque modules are Cech-acyclic"]
theorem isAcyclic_of_flasque
    (ℱ : X.Modules) (hℱ : Modules.flasque X ℱ) :
    IsAcyclic ℱ := sorry

end ModuleCech



end AlgebraicGeometry.RingedSpace

end
