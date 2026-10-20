/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.NoetherianIrreducibleComponents
import StacksCheckRecall

@[expose] public section

/- Exercise 111.6.20 (1): a Noetherian topological space `X` has only finitely many irreducible
components. -/
@[stacks 02DB]
#check (TopologicalSpace.NoetherianSpace.finite_irreducibleComponents_of_noetherian :
  ∀ {X : Type*} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X],
    (irreducibleComponents X).Finite)

/- Exercise 111.6.20 (2): `X` is the union of its irreducible components. This covering holds for
every topological space, not just Noetherian ones. (The parenthetical that the usual topology on `ℝ` has singleton
irreducible components is pedagogical and is not a third source clause.) -/
@[stacks 02DB]
#check (TopologicalSpace.sUnion_irreducibleComponents :
  ∀ {X : Type*} [TopologicalSpace X], ⋃₀ irreducibleComponents X = Set.univ)
