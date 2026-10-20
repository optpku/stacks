/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Constructible.Specialization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 5.19.10

Constructible specialization/generalization API is owned by
`ReasLib.Topology.Constructible.Specialization`.
-/

/- Lemma 5.19.10: the reusable quasi-sober specialization-stability criterion. -/
@[stacks 0542 "constructible and specialization-stable implies closed"]
#check @Topology.IsConstructible.isClosed_of_stableUnderSpecialization

/- Lemma 5.19.10: the reusable quasi-sober generalization-stability criterion. -/
@[stacks 0542 "constructible and generalization-stable implies open"]
#check @Topology.IsConstructible.isOpen_of_stableUnderGeneralization
