/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Constructible
import StacksCheckRecall

@[expose] public section

/-
`Topology.IsConstructible` is the canonical property owner: its Boolean-subalgebra presentation
has the source's finite-union-of-`U ∩ Vᶜ` presentation as the finite Boolean normal form for open
retrocompact subsets. `Topology.IsLocallyConstructible` is the canonical local owner: choosing one
of its open neighborhood witnesses at every point gives the source's open cover, while any such
cover supplies those pointwise witnesses. Direct recalls therefore recover both source clauses
without a parallel predicate and expose mathlib's closure and functoriality API downstream.
-/

/- Definition 5.15.1 (1): a subset is constructible when it is a finite union of sets `U ∩ Vᶜ`
with `U` and `V` open and retrocompact. -/
@[stacks 005G "constructible subsets"]
#check Topology.IsConstructible

/- Definition 5.15.1 (2): a subset is locally constructible when an open cover has constructible
traces in its members. -/
@[stacks 005G "locally constructible subsets"]
#check Topology.IsLocallyConstructible
