/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Specialization.Dimension
import StacksCheckRecall

@[expose] public section

universe u

open Specialization TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/- Definition 5.20.1 (1): immediate specialization is the source-facing presentation of a cover
relation in the specialization order. -/
@[stacks 02I9 "immediate specializations"]
#check (IsImmediateSpecialization : X → X → Prop)

/- Definition 5.20.1 (2): a dimension function is an integer-valued function with the prescribed
strict-specialization and immediate-specialization behaviour. -/
@[stacks 02I9 "dimension functions"]
#check (IsDimensionFunction : (X → ℤ) → Prop)
