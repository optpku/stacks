module

public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Topology.Sets.OpenCover
public import ReasLib.AlgebraicTopology.SimplicialSet.OpenHypercovering.Matching
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Intersection conditions for open hypercoverings

This module owns the finite-intersection open-cover condition used by open hypercoverings.  The
compatibility predicate is explicit: Stacks' higher matching equation quantifies only over
compatible boundary tuples, while a compatible tuple may still have an empty matching fiber.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u v w

namespace SSet

namespace OpenHypercovering

variable {X : Type u} [TopologicalSpace X]
variable {n : ℕ} {In : Type v} {In1 : Type w}

end OpenHypercovering
end SSet

namespace TopologicalSpace.Opens

variable {X : Type u} [TopologicalSpace X]
variable {n : ℕ} {In : Type v} {In1 : Type w}

namespace IndexedIntersection

/-- The subtype of tuples selected by an indexed intersection's compatibility predicate. -/
abbrev CompatibleTuple
    (compatible : (Fin (n + 2) → In) → Prop) :=
  {i : Fin (n + 2) → In // compatible i}

end IndexedIntersection

/-- A finite indexed family of opens covers each compatible prescribed intersection.

This is the neutral lattice-level owner; hypercoverings use its boundary-compatible
specialization. -/
structure IndexedIntersection
    (d : Fin (n + 2) → In1 → In) (Un : In → Opens X) (Un1 : In1 → Opens X)
    (compatible : (Fin (n + 2) → In) → Prop) : Prop where
  /-- The matching level-`n + 1` opens cover the prescribed finite intersection. -/
  iInf_eq_iSup (i : IndexedIntersection.CompatibleTuple compatible) :
    (⨅ a, Un (i.1 a)) =
      iSup (fun j : SSet.OpenHypercovering.MatchingIndices d i.1 ↦ Un1 j)

end TopologicalSpace.Opens

namespace SSet

namespace OpenHypercovering

variable {X : Type u} [TopologicalSpace X]
variable {n : ℕ} {In : Type v} {In1 : Type w}

namespace Intersection

/-- The subtype of boundary tuples selected by an intersection condition's compatibility
predicate. -/
abbrev CompatibleTuple
    (compatible : (Fin (n + 2) → In) → Prop) :=
  TopologicalSpace.Opens.IndexedIntersection.CompatibleTuple compatible

end Intersection

/-- A generic indexed-intersection condition, exposed under the historical hypercovering path as a
thin bridge to `TopologicalSpace.Opens.IndexedIntersection`. -/
abbrev Intersection
    (d : Fin (n + 2) → In1 → In) (Un : In → Opens X) (Un1 : In1 → Opens X)
    (compatible : (Fin (n + 2) → In) → Prop) : Prop :=
  TopologicalSpace.Opens.IndexedIntersection d Un Un1 compatible

/-- The canonical hypercovering intersection condition, with compatibility fixed to the matching
boundary predicate of the index simplicial set. -/
@[stacks 01H4 "boundary-compatible hypercovering intersection"]
abbrev BoundaryIntersection
    {I : SSet.{v}} {n : ℕ}
    (Un : I.obj (op <| SimplexCategory.mk n) → Opens X)
    (Un1 : I.obj (op <| SimplexCategory.mk (n + 1)) → Opens X) : Prop :=
  Intersection
    (fun a j => I.δ a j) Un Un1 (Boundary.Compatible I)

namespace Intersection

/-- The matching-cover equality expressed as a supremum over the range of matching opens. -/
theorem iInf_eq_sSup
    {d : Fin (n + 2) → In1 → In} {Un : In → Opens X} {Un1 : In1 → Opens X}
    {compatible : (Fin (n + 2) → In) → Prop}
    (h : Intersection d Un Un1 compatible) (i : CompatibleTuple compatible) :
    (⨅ a, Un (i.1 a)) = sSup (Set.range (fun j : MatchingIndices d i.1 ↦ Un1 j)) := sorry

/-- A matching level-`n + 1` open lies in the corresponding finite intersection. -/
theorem matchingOpen_le_iInf
    {d : Fin (n + 2) → In1 → In} {Un : In → Opens X} {Un1 : In1 → Opens X}
    {compatible : (Fin (n + 2) → In) → Prop}
    (h : Intersection d Un Un1 compatible) (i : CompatibleTuple compatible)
    (j : MatchingIndices d i.1) :
    Un1 j ≤ ⨅ a, Un (i.1 a) := sorry

/-- A matching level-`n + 1` open lies in each factor of the corresponding finite intersection. -/
theorem matchingOpen_le
    {d : Fin (n + 2) → In1 → In} {Un : In → Opens X} {Un1 : In1 → Opens X}
    {compatible : (Fin (n + 2) → In) → Prop}
    (h : Intersection d Un Un1 compatible) (i : CompatibleTuple compatible)
    (j : MatchingIndices d i.1) (a : Fin (n + 2)) :
    Un1 j ≤ Un (i.1 a) := sorry

/-- If there are no matching indices, the finite intersection they are required to cover is
empty.  Thus an empty matching family is permitted precisely at an empty intersection. -/
@[stacks 01H5 "empty matching covering"]
theorem iInf_eq_bot_of_isEmpty_matchingIndices
    {d : Fin (n + 2) → In1 → In} {Un : In → Opens X} {Un1 : In1 → Opens X}
    {compatible : (Fin (n + 2) → In) → Prop}
    (h : Intersection d Un Un1 compatible) (i : CompatibleTuple compatible)
    [IsEmpty (MatchingIndices d i.1)] :
    (⨅ a, Un (i.1 a)) = ⊥ := sorry

/-- The empty-intersection consequence with an explicit proposition instead of an `IsEmpty`
instance.  This form is convenient for downstream statements that should not rebuild a local
instance for a matching fiber. -/
@[stacks 01H5 "empty matching fiber without a local instance"]
theorem iInf_eq_bot_of_not_nonempty
    {d : Fin (n + 2) → In1 → In} {Un : In → Opens X} {Un1 : In1 → Opens X}
    {compatible : (Fin (n + 2) → In) → Prop}
    (h : Intersection d Un Un1 compatible) (i : CompatibleTuple compatible)
    (h_empty : ¬ Nonempty (MatchingIndices d i.1)) :
    (⨅ a, Un (i.1 a)) = ⊥ := sorry

/-- An empty matching family covers a prescribed finite intersection whenever that intersection
is empty. -/
@[stacks 01H5 "empty matching covering"]
theorem emptyCover
    {d : Fin (n + 2) → In1 → In} {Un : In → Opens X} {Un1 : In1 → Opens X}
    {compatible : (Fin (n + 2) → In) → Prop}
    (i : CompatibleTuple compatible) (hi : (⨅ a, Un (i.1 a)) = ⊥)
    [IsEmpty (MatchingIndices d i.1)] :
    (⨅ a, Un (i.1 a)) = iSup (fun j : MatchingIndices d i.1 ↦ Un1 j) := sorry

/-- The empty matching-cover equality with an explicit proposition instead of an `IsEmpty`
instance. -/
@[stacks 01H5 "empty matching cover without a local instance"]
theorem emptyCover_of_not_nonempty
    {d : Fin (n + 2) → In1 → In} {Un : In → Opens X} {Un1 : In1 → Opens X}
    {compatible : (Fin (n + 2) → In) → Prop}
    (i : CompatibleTuple compatible) (hi : (⨅ a, Un (i.1 a)) = ⊥)
    (h_empty : ¬ Nonempty (MatchingIndices d i.1)) :
    (⨅ a, Un (i.1 a)) = iSup (fun j : MatchingIndices d i.1 ↦ Un1 j) := sorry

/-- A nonempty finite intersection covered by matching opens has at least one matching index. -/
theorem nonempty_matchingIndices_of_iInf_ne_bot
    {d : Fin (n + 2) → In1 → In} {Un : In → Opens X} {Un1 : In1 → Opens X}
    {compatible : (Fin (n + 2) → In) → Prop}
    (h : Intersection d Un Un1 compatible) (i : CompatibleTuple compatible)
    (hi : (⨅ a, Un (i.1 a)) ≠ ⊥) :
    Nonempty (MatchingIndices d i.1) := sorry

/-- Membership in a prescribed finite intersection is equivalent to membership in a matching open. -/
theorem mem_iInf_iff_exists
    {d : Fin (n + 2) → In1 → In} {Un : In → Opens X} {Un1 : In1 → Opens X}
    {compatible : (Fin (n + 2) → In) → Prop}
    (h : Intersection d Un Un1 compatible) (i : CompatibleTuple compatible) (x : X) :
    x ∈ (⨅ a, Un (i.1 a) : Opens X) ↔
      ∃ j : MatchingIndices d i.1, x ∈ Un1 j := sorry

/-- The matching-cover equality in finite-inf notation. -/
theorem eq_iSup
    {d : Fin (n + 2) → In1 → In} {Un : In → Opens X} {Un1 : In1 → Opens X}
    {compatible : (Fin (n + 2) → In) → Prop}
    (h : Intersection d Un Un1 compatible) (i : CompatibleTuple compatible) :
    Finset.univ.inf (fun a : Fin (n + 2) ↦ Un (i.1 a)) =
      iSup (fun j : MatchingIndices d i.1 ↦ Un1 j) := sorry

/-- The matching-cover equality in finite-inf and set-indexed-supremum notation. -/
theorem eq_sSup
    {d : Fin (n + 2) → In1 → In} {Un : In → Opens X} {Un1 : In1 → Opens X}
    {compatible : (Fin (n + 2) → In) → Prop}
    (h : Intersection d Un Un1 compatible) (i : CompatibleTuple compatible) :
    Finset.univ.inf (fun a : Fin (n + 2) ↦ Un (i.1 a)) =
      sSup (Set.range (fun j : MatchingIndices d i.1 ↦ Un1 j)) := sorry

end Intersection

/-- The two-face specialization of the finite-intersection condition. -/
@[stacks 01H3 "pairwise hypercovering condition"]
abbrev PairwiseIntersection
    (d0 d1 : In1 → In) (U0 : In → Opens X) (U1 : In1 → Opens X) : Prop :=
  Intersection ![d0, d1] U0 U1 (fun _ : Fin 2 → In ↦ True)

namespace PairwiseIntersection

/-- The pairwise matching-cover equality attached to a two-face intersection condition. -/
theorem inf_eq_iSup
    {d0 d1 : In1 → In} {U0 : In → Opens X} {U1 : In1 → Opens X}
    (h : PairwiseIntersection d0 d1 U0 U1)
    (i0 i1 : In) :
    U0 i0 ⊓ U0 i1 =
      iSup (fun i : { i : In1 // d0 i = i0 ∧ d1 i = i1 } ↦ U1 i.1) := sorry

end PairwiseIntersection
end OpenHypercovering
end SSet
