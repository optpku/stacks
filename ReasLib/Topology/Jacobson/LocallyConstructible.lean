/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.Constructible.LocallyClosedUnion
public import ReasLib.Topology.Jacobson.LocallyClosed

/-!
# Jacobson Locally Constructible Subspaces

Constructible specializations of the locally-closed-union Jacobson subspace
API live separately from the topology-only owner.
-/

@[expose] public section

universe u

open Set TopologicalSpace Topology
open scoped Set.Notation

variable {X : Type u} [TopologicalSpace X]

namespace Topology.IsLocallyConstructible

/-- Lemma 5.18.5: a locally constructible subspace of a Jacobson space is
Jacobson. -/
@[stacks 005X "Jacobson locally constructible subspaces"]
theorem jacobsonSpace_subtype [JacobsonSpace X] {T : Set X}
    (hT : IsLocallyConstructible T) : JacobsonSpace T := sorry

/-- Lemma 5.18.5: closed points of a locally constructible subspace of a
Jacobson space remain closed in the ambient space. -/
@[stacks 005X "closed points of locally constructible subspaces"]
theorem closedPoints_subset_preimage_closedPoints [JacobsonSpace X] {T : Set X}
    (hT : IsLocallyConstructible T) :
    closedPoints T ⊆ T ↓∩ closedPoints X := sorry

end Topology.IsLocallyConstructible

namespace Topology.IsConstructible

/-- Lemma 5.18.5 (5): a constructible subspace of a Jacobson space is Jacobson. -/
@[stacks 005X "(5) constructible subspaces are Jacobson"]
theorem jacobsonSpace_subtype [JacobsonSpace X] {T : Set X}
    (hT : IsConstructible T) : JacobsonSpace T := sorry

/-- Lemma 5.18.5 (5): closed points of a constructible subspace are ambiently closed. -/
@[stacks 005X "(5) closed points of constructible subspaces"]
theorem closedPoints_subset_preimage_closedPoints [JacobsonSpace X] {T : Set X}
    (hT : IsConstructible T) :
    closedPoints T ⊆ T ↓∩ closedPoints X := sorry

end Topology.IsConstructible
