/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Category.TopCat.Basic
public import Mathlib.Topology.Sheaves.SheafOfFunctions

/-!
# Sectionwise-discrete presheaves

For a family of types on the points of a topological space, this file constructs the presheaf of
dependent functions whose section spaces have the discrete topology.  It distinguishes this
sectionwise topology from the product topology on the same underlying dependent-function spaces.

## API under `TopCat.Presheaf.SectionwiseDiscrete`

- `presheaf A` — dependent-function sections with the discrete topology
- `underlying_isSheaf` — forgetting topology recovers a sheaf of types
- `not_isSheaf_of_infinite_discrete` — the topological presheaf is not generally a sheaf
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u v

namespace TopCat.Presheaf.SectionwiseDiscrete

variable {X : TopCat.{u}}

/-- The presheaf of dependent functions with the discrete topology on each section space. -/
abbrev presheaf (A : X → Type v) : X.Presheaf TopCat.{max u v} :=
  X.presheafToTypes A ⋙ TopCat.discrete

/-- After forgetting topology, the sectionwise-discrete presheaf is a sheaf of types. -/
theorem underlying_isSheaf (A : X → Type v) :
    TopCat.Presheaf.IsSheaf (presheaf A ⋙ CategoryTheory.forget TopCat) := sorry

/-- On an infinite discrete space, a sectionwise-discrete presheaf with nontrivial fibers is not
a sheaf of topological spaces. -/
theorem not_isSheaf_of_infinite_discrete (A : X → Type v)
    [DiscreteTopology X] [Infinite X] [∀ x, Nontrivial (A x)] :
    ¬ (presheaf A).IsSheaf := sorry

end TopCat.Presheaf.SectionwiseDiscrete
