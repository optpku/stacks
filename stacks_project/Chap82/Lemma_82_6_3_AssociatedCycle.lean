/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.LocallyFinsupp
public import stacks_project.Chap65.Definition_65_12_1_Subspace
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap66.Lemma_66_4_6_Topology
import stacks_project.Chap82.Definition_82_5_2_AssociatedCycle

/-!
# Associated cycles of closed subspaces, import-isolated

`Hom.closedSubspaceCycle` is definitionally `ClosedSubspace.associatedCycle` for the
relative dimension function, but Definition 82.5.2 also redefines
`Hom.closedSubspaceDeltaDimension` and cannot be loaded beside `Hom.moduleCycle`.
This module exposes that associated-cycle data without re-exporting the conflicting
dimension names.
-/

public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.ClosedSubspace

/-- The multiplicity-weighted degree-`k` cycle of a closed subspace, as a locally
finite integer function on `|X|`. -/
noncomputable def cycle {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (Y : ClosedSubspace X) (d : Points X → ℤ) (k : ℤ) :
    Function.locallyFinsupp (Points X) ℤ :=
  associatedCycle Y d k

/-- Off the dimension-`k` locus, the closed-subspace cycle coefficient vanishes. -/
theorem cycle_eq_zero_of_dimension_ne {S : Scheme.{u}} {X : AlgebraicSpace S}
    [IsLocallyNoetherian X] (Y : ClosedSubspace X) (d : Points X → ℤ) (k : ℤ)
    {x : Points X} (hx : d x ≠ k) : cycle Y d k x = 0 :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.ClosedSubspace
