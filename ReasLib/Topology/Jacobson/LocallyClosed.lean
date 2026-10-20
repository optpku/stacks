/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Topology.LocallyClosed.LocalUnion

/-!
# Jacobson Subspaces from Locally Closed Unions

Jacobson-space inheritance is stated on the locally union-of-locally-closed
predicate. Constructible specializations live in a separate leaf.
-/

@[expose] public section

universe u

open Set TopologicalSpace Topology
open scoped Set.Notation

variable {X : Type u} [TopologicalSpace X]

namespace IsLocallyUnionOfLocallyClosed

/-- Lemma 5.18.5 (1): a locally union-of-locally-closed subspace of a
Jacobson space is Jacobson. -/
@[stacks 005X "Jacobson subspaces from locally closed unions"]
theorem jacobsonSpace_subtype [JacobsonSpace X] {T : Set X}
    (hT : IsLocallyUnionOfLocallyClosed T) : JacobsonSpace T := sorry

/-- Lemma 5.18.5 (2): closed points of a locally union-of-locally-closed
subspace of a Jacobson space remain closed in the ambient space. -/
@[stacks 005X "closed points remain closed in the ambient Jacobson space"]
theorem closedPoints_subset_preimage_closedPoints [JacobsonSpace X] {T : Set X}
    (hT : IsLocallyUnionOfLocallyClosed T) :
    closedPoints T ⊆ T ↓∩ closedPoints X := sorry

end IsLocallyUnionOfLocallyClosed

namespace IsUnionOfLocallyClosed

/-- Lemma 5.18.5 (4): a union of locally closed subspaces of a Jacobson space is Jacobson. -/
@[stacks 005X "(4) unions of locally closed subspaces are Jacobson"]
theorem jacobsonSpace_subtype [JacobsonSpace X] {T : Set X}
    (hT : IsUnionOfLocallyClosed T) : JacobsonSpace T := sorry

/-- Lemma 5.18.5 (4): closed points of a union of locally closed subspaces are ambiently closed. -/
@[stacks 005X "(4) closed points of unions of locally closed subspaces"]
theorem closedPoints_subset_preimage_closedPoints [JacobsonSpace X] {T : Set X}
    (hT : IsUnionOfLocallyClosed T) :
    closedPoints T ⊆ T ↓∩ closedPoints X := sorry

end IsUnionOfLocallyClosed

namespace IsOpen

/- The first four source cases are exposed as direct methods so callers do not
have to manually pass through the weakest locally-union predicate. -/

/-- Lemma 5.18.5 (1): an open subspace of a Jacobson space is Jacobson. -/
@[stacks 005X "(1) open subspaces are Jacobson"]
theorem jacobsonSpace_subtype [JacobsonSpace X] {T : Set X}
    (hT : IsOpen T) : JacobsonSpace T := sorry

/-- Lemma 5.18.5 (1): closed points of an open subspace are ambiently closed. -/
@[stacks 005X "(1) closed points of open subspaces"]
theorem closedPoints_subset_preimage_closedPoints [JacobsonSpace X] {T : Set X}
    (hT : IsOpen T) :
    closedPoints T ⊆ T ↓∩ closedPoints X := sorry

end IsOpen

namespace IsClosed

/-- Lemma 5.18.5 (2): a closed subspace of a Jacobson space is Jacobson. -/
@[stacks 005X "(2) closed subspaces are Jacobson"]
theorem jacobsonSpace_subtype [JacobsonSpace X] {T : Set X}
    (hT : IsClosed T) : JacobsonSpace T := sorry

/-- Lemma 5.18.5 (2): closed points of a closed subspace are ambiently closed. -/
@[stacks 005X "(2) closed points of closed subspaces"]
theorem closedPoints_subset_preimage_closedPoints [JacobsonSpace X] {T : Set X}
    (hT : IsClosed T) :
    closedPoints T ⊆ T ↓∩ closedPoints X := sorry

end IsClosed

namespace IsLocallyClosed

/-- Lemma 5.18.5 (3): a locally closed subspace of a Jacobson space is Jacobson. -/
@[stacks 005X "(3) locally closed subspaces are Jacobson"]
theorem jacobsonSpace_subtype [JacobsonSpace X] {T : Set X}
    (hT : IsLocallyClosed T) : JacobsonSpace T := sorry

/-- Lemma 5.18.5 (3): closed points of a locally closed subspace are ambiently closed. -/
@[stacks 005X "(3) closed points of locally closed subspaces"]
theorem closedPoints_subset_preimage_closedPoints [JacobsonSpace X] {T : Set X}
    (hT : IsLocallyClosed T) :
    closedPoints T ⊆ T ↓∩ closedPoints X := sorry

end IsLocallyClosed
