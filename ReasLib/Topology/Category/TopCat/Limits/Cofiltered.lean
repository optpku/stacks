/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.Topology.Category.TopCat.Limits.Cofiltered
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Topology.Sets.Compacts
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Cofiltered Limits of Topological Spaces

Reusable descent API for cofiltered limits in `TopCat`. General limit
recognition and compactness belong to `Limits.Recognition` and
`Limits.Compact` respectively.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Set TopologicalSpace

universe u v w

namespace TopCat

namespace IsLimit

variable {J : Type v} [Category.{w} J] [IsCofiltered J]
variable {F : J ⥤ TopCat.{max v u}} {C : Cone F}

/-- Lemma 5.14.2 (1): an open subset of a cofiltered limit is the union of
stagewise pullbacks of open subsets. -/
@[stacks 0A2P "opens are unions of stagewise pullbacks"]
theorem open_eq_iUnion_preimage (hC : IsLimit C) (W : Opens C.pt) :
    ∃ U : ∀ j, Opens (F.obj j), (W : Set C.pt) = ⋃ j, C.π.app j ⁻¹' (U j : Set (F.obj j)) := sorry

/-- Lemma 5.14.2 (2): a compact open subset of a cofiltered limit is pulled
back from one stage. -/
@[stacks 0A2P "quasi-compact opens descend to one stage"]
theorem compactOpen_eq_preimage (hC : IsLimit C) (W : CompactOpens C.pt) :
    ∃ (j : J) (U : Opens (F.obj j)), (W : Set C.pt) = C.π.app j ⁻¹' (U : Set (F.obj j)) := sorry

end IsLimit

end TopCat
