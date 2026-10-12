/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Cohomology
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cohomological acyclicity on families of opens

This leaf records positive-degree vanishing on a chosen family of opens.  The primary owner keeps
the natural module structure over each section ring; the underlying additive-sheaf formulation is
available through a named comparison.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.ModuleCohomology

variable {X : RingedSpace.{u}}

/-- A module sheaf is cohomologically acyclic on every open belonging to `B`. -/
@[stacks 08C2 "module cohomology acyclicity on a family of opens"]
def IsAcyclicOn (F : X.Modules) (B : Set (Opens X.carrier)) : Prop :=
  ∀ ⦃U : Opens X.carrier⦄, U ∈ B → ∀ p : ℕ, 0 < p →
    IsZero (moduleCohomologyAtOpen U F p)

namespace IsAcyclicOn

/-- Specialize acyclicity to one open and one positive cohomological degree. -/
@[stacks 08C2 "specialization of module cohomology acyclicity"]
theorem isZero {F : X.Modules} {B : Set (Opens X.carrier)}
    (hF : IsAcyclicOn F B) {U : Opens X.carrier} (hU : U ∈ B)
    (p : ℕ) (hp : 0 < p) :
    IsZero (moduleCohomologyAtOpen U F p) := sorry

end IsAcyclicOn

variable [HasSheafify (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u}]
variable [HasExt (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/-- The underlying additive-sheaf form of cohomological acyclicity on `B`. -/
@[stacks 08C2 "underlying sheaf cohomology acyclicity on a family of opens"]
def IsUnderlyingAcyclicOn (F : X.Modules) (B : Set (Opens X.carrier)) : Prop :=
  ∀ ⦃U : Opens X.carrier⦄, U ∈ B → ∀ p : ℕ, 0 < p →
    IsZero (((moduleUnderlyingSheaf X).obj F).H' p U)

/-- Module-valued and underlying additive formulations of acyclicity on `B` agree. -/
@[stacks 08C2 "module and underlying sheaf acyclicity comparison"]
theorem isAcyclicOn_iff_underlying (F : X.Modules) (B : Set (Opens X.carrier)) :
    IsAcyclicOn F B ↔ IsUnderlyingAcyclicOn F B := sorry

end AlgebraicGeometry.RingedSpace.ModuleCohomology
