/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.JacobsonSpace
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/- Lemma 5.18.6 (1): a finite Jacobson space is discrete. -/
@[stacks 07JU "finite Jacobson spaces are discrete"]
#check fun [Finite X] [JacobsonSpace X] ↦ (inferInstance : DiscreteTopology X)

/- Lemma 5.18.6 (2): a Jacobson space with finitely many closed points is discrete. -/
@[stacks 07JU "finitely many closed points force a Jacobson space to be discrete"]
#check JacobsonSpace.discreteTopology
