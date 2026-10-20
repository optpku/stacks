/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.OpenCover.LocallyFinite
import StacksCheckRecall

@[expose] public section

universe u v

variable {X : Type u} [TopologicalSpace X] {ι : Type v}

/- Definition 20.24.2: an open covering `X = ⋃ i, U i` is locally finite if every
point has an open neighbourhood meeting only finitely many members `U i`. This is
identified with `IsOpenCover U ∧ LocallyFinite (Opens.asSets U)` via
`TopologicalSpace.locallyFiniteCover_iff`. -/
@[stacks 02FS]
#check (TopologicalSpace.locallyFiniteCover_iff :
  ∀ U : ι → TopologicalSpace.Opens X,
    (TopologicalSpace.IsOpenCover U ∧ LocallyFinite (TopologicalSpace.Opens.asSets U)) ↔
      TopologicalSpace.IsOpenCover U ∧
        ∀ x : X, ∃ W : TopologicalSpace.Opens X, x ∈ W ∧ {i | W.Meets (U i)}.Finite)
