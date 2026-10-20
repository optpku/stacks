/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.IrreducibleComponents
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.9.2

The component-neighbourhood API is owned by
`ReasLib.Topology.IrreducibleComponents`; the three source clauses are Mathlib recalls.
-/

/- Lemma 5.9.2 (1): every subspace of a Noetherian topological space is Noetherian. -/
@[stacks 0052 "Noetherianity of subspaces"]
#check @TopologicalSpace.NoetherianSpace.set

/- Lemma 5.9.2 (2): a Noetherian topological space has only finitely many irreducible
components. -/
@[stacks 0052 "finiteness of irreducible components"]
#check @TopologicalSpace.NoetherianSpace.finite_irreducibleComponents

/- Lemma 5.9.2 (3): every irreducible component of a Noetherian topological space contains a
nonempty open subset of the ambient space. -/
@[stacks 0052 "nonempty ambient opens inside irreducible components"]
#check @TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
