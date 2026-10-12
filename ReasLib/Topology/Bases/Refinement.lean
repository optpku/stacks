/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Topology.Sets.Opens
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Refining Opens and Open Covers by Bases

Canonical decompositions of opens, and refinements of indexed open covers, by members of a
topological basis.
-/

@[expose] public section

universe u v

open Set

namespace TopologicalSpace.IsTopologicalBasis

variable {X : Type u} [TopologicalSpace X]

/-- Lemma 5.5.3: an indexed open cover of an open subset admits a refinement by members of a
topological basis. -/
@[stacks 004Q "basis refinement of an indexed open cover"]
theorem exists_refinement_of_openCover
    {ι : Type v} {B : Set (Set X)} (hB : IsTopologicalBasis B)
    (U : Opens X) (Ui : ι → Opens X) (hUi : (U : Set X) = ⋃ i, (Ui i : Set X)) :
    ∃ (J : Type (max u v)) (V : J → {V : Set X // V ∈ B}),
      (U : Set X) = ⋃ j, (V j : Set X) ∧ ∀ j, ∃ i, (V j : Set X) ⊆ Ui i := sorry

end TopologicalSpace.IsTopologicalBasis

namespace TopologicalSpace.Opens

variable {X : Type u} [TopologicalSpace X]

/-- Every open is the supremum of the basis opens contained in it. -/
theorem IsBasis.eq_sSup {B : Set (Opens X)} (hB : IsBasis B) (U : Opens X) :
    U = sSup {V : Opens X | V ∈ B ∧ V ≤ U} := sorry

/-- Every open is the supremum of its contained basis opens, indexed by that subtype. -/
@[stacks 071K "basis-open supremum"]
theorem IsBasis.eq_iSup {B : Set (Opens X)} (hB : IsBasis B) (U : Opens X) :
    U = iSup (fun V : {V : Opens X // V ∈ B ∧ V ≤ U} ↦ (V : Opens X)) := sorry

end TopologicalSpace.Opens
