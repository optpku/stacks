/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Bases
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Generating Topologies from Bases

Construction and uniqueness API for topologies presented by a basis family.
-/

@[expose] public section

universe u

open Set FiniteInter

namespace TopologicalSpace

variable {X : Type u}

/-- A covering family with the basis-intersection refinement property is a topological basis for
the topology it generates. -/
theorem isTopologicalBasis_generateFrom (B : Set (Set X)) (hcover : sUnion B = univ)
    (hinter :
      ∀ ⦃x : X⦄ ⦃U : Set X⦄, U ∈ B → ∀ ⦃V : Set X⦄, V ∈ B →
        x ∈ U ∩ V → ∃ W ∈ B, x ∈ W ∧ W ⊆ U ∩ V) :
    @IsTopologicalBasis X (generateFrom B) B := sorry

/-- Lemma 5.5.2: a covering family with basis-intersection refinements determines a unique
topology for which it is a topological basis. -/
@[stacks 0D5P "unique topology determined by the covering refinement family"]
theorem existsUnique_topology_with_basis (B : Set (Set X)) (hcover : sUnion B = univ)
    (hinter :
      ∀ ⦃x : X⦄ ⦃U : Set X⦄, U ∈ B → ∀ ⦃V : Set X⦄, V ∈ B →
        x ∈ U ∩ V → ∃ W ∈ B, x ∈ W ∧ W ⊆ U ∩ V) :
    ∃! t : TopologicalSpace X, @IsTopologicalBasis X t B := sorry

variable [t : TopologicalSpace X]

/-- Definition 5.5.4: a family generates the ambient topology exactly when its finite
intersection closure is a topological basis. -/
@[stacks 08ZI "subbases through finite-intersection basis closure"]
theorem eq_generateFrom_iff_isTopologicalBasis_finiteInterClosure {B : Set (Set X)} :
    t = generateFrom B ↔ IsTopologicalBasis (finiteInterClosure B) := sorry

end TopologicalSpace
