/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Topology.Jacobson.ClosedPoints

/-!
# Surjectivity detected on closed points of Jacobson spaces

Open subsets and open ranges in a Jacobson space are determined by their closed points.
-/

@[expose] public section

open scoped Set.Notation

universe u

namespace IsOpen

/-- An open subset of a Jacobson space that contains every closed point is the whole space. -/
theorem eq_univ_of_closedPoints_subset
    {X : Type u} [TopologicalSpace X] [JacobsonSpace X]
    {U : Set X} (hU : IsOpen U) (hclosed : closedPoints X ⊆ U) :
    U = Set.univ := by
  have hUfinite : IsFiniteUnionOfLocallyClosed U :=
    hU.isLocallyClosed.isFiniteUnionOfLocallyClosed
  have htrace :
      (closedPoints X) ↓∩ Set.univ ⊆ (closedPoints X) ↓∩ U := by
    intro x hx
    simpa using hclosed x.2
  have hsubset : Set.univ ⊆ U :=
    (IsFiniteUnionOfLocallyClosed.closedPointsTrace_subset_iff
      (X := X) IsFiniteUnionOfLocallyClosed.univ hUfinite).mp htrace
  exact Set.eq_univ_iff_forall.mpr fun x ↦ hsubset (by simp)

end IsOpen

namespace Function.Surjective

/-- A map into a Jacobson space is surjective if its range is open and contains every closed
point. -/
theorem of_isOpen_range_of_closedPoints
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] [JacobsonSpace Y]
    {f : X → Y} (hopen : IsOpen (Set.range f)) (hclosed : closedPoints Y ⊆ Set.range f) :
    Function.Surjective f := by
  have hRange : Set.range f = Set.univ :=
    hopen.eq_univ_of_closedPoints_subset hclosed
  intro y
  have hy : y ∈ Set.range f := by
    rw [hRange]
    simp
  exact hy

end Function.Surjective
