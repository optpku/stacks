/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sets.OpenCover
import StacksCheckRecall

@[expose] public section

open TopologicalSpace

universe u v

variable {X : Type u} [TopologicalSpace X] {I₀ : Type v} (U₀ : I₀ → Opens X)

/- Equation 25.11.0.1: the degree-`0` opens form an open cover. -/
@[stacks 01H2]
#check (IsOpenCover U₀ : Prop)

/- The corresponding source-facing union equality is the canonical open-cover theorem. -/
#check @IsOpenCover.iSup_set_eq_univ
