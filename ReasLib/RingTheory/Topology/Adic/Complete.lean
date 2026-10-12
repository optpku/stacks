/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.AdicCompletion.Topology
public import ReasLib.RingTheory.Topology.Adic.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Complete admissible and adic topological rings

@stack 07E8
-/

@[expose] public section

open scoped Topology

universe u

namespace TopologicalRing

section

variable {R : Type u} [CommRing R] [TopologicalSpace R]

/-- An admissible topological ring is a complete separated pre-admissible topological ring. -/
@[stacks 07E8 "(6), admissible ring"]
class IsAdmissibleRing (R : Type u) [CommRing R] [TopologicalSpace R] : Prop
    extends IsPreadmissibleRing R where
  /-- The ambient topology is separated. -/
  isT2 : T2Space R
  /-- The ambient additive uniformity is complete. -/
  isComplete : @CompleteSpace R (IsTopologicalAddGroup.rightUniformSpace R)

/-- An admissible topological ring is separated. -/
@[stacks 07E8 "separatedness of an admissible ring"]
instance instT2Space [IsAdmissibleRing R] : T2Space R := sorry

/-- An admissible topological ring is complete for its additive uniformity. -/
@[stacks 07E8 "completeness of an admissible ring"]
instance instCompleteSpace [IsAdmissibleRing R] :
    @CompleteSpace R (IsTopologicalAddGroup.rightUniformSpace R) := sorry

/-- An adic topological ring has a complete and separated defining adic ideal. -/
@[stacks 07E8 "(8), adic ring"]
class IsAdicRing (R : Type u) [CommRing R] [TopologicalSpace R] : Prop
    extends IsTopologicalRing R where
  /-- An adic ring has a complete defining adic ideal. -/
  exists_ideal_isAdicComplete : ∃ I : Ideal R, IsAdic I ∧ IsAdicComplete I R

/-- Adic completeness supplies completeness and separatedness for the ambient additive
uniformity. -/
@[stacks 07E8 "adic completeness gives complete separated topology"]
theorem complete_space_and_t2_of_is_adic_complete [IsTopologicalRing R] {I : Ideal R}
    (hI : IsAdic I) (hIComplete : IsAdicComplete I R) :
    @CompleteSpace R (IsTopologicalAddGroup.rightUniformSpace R) ∧ T2Space R := sorry

/-- An adic ring is pre-adic after forgetting completeness. -/
@[stacks 07E8 "an adic ring is pre-adic"]
instance instIsPreadicRing [IsAdicRing R] : IsPreadicRing R := sorry

/-- An adic ring is separated. -/
@[stacks 07E8 "separatedness of an adic ring"]
instance instT2SpaceOfIsAdicRing [IsAdicRing R] : T2Space R := sorry

/-- An adic ring is complete for its ambient additive uniformity. -/
@[stacks 07E8 "completeness of an adic ring"]
instance instCompleteSpaceOfIsAdicRing [IsAdicRing R] :
    @CompleteSpace R (IsTopologicalAddGroup.rightUniformSpace R) := sorry

/-- An adic ring is admissible after forgetting the chosen complete adic ideal. -/
@[stacks 07E8 "an adic ring is admissible"]
instance instIsAdmissibleRing [IsAdicRing R] : IsAdmissibleRing R := sorry

end

end TopologicalRing
