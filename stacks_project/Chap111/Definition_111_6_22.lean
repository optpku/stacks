/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Topology.Point
public import Mathlib.Topology.Inseparable
import StacksCheckRecall

@[expose] public section

universe u

/- Definition 111.6.22 (1): a point `x` of a topological space `X` is closed when
`closure {x} = {x}`. -/
@[stacks 027H]
#check (Topology.mem_closedPoints_iff_closure_eq :
  ∀ {X : Type u} [TopologicalSpace X] (x : X),
    x ∈ closedPoints X ↔ closure ({x} : Set X) = {x})

/- Definition 111.6.22 (2): for points `x`, `y` of `X`, `x` is a specialization of `y`, or
`y` is a generalization of `x`, when `x ∈ closure {y}`. In mathlib argument order,
this is `Specializes y x`, written `y ⤳ x`, identified with `x ∈ closure {y}` by
mathlib's `specializes_iff_mem_closure`. -/
@[stacks 027H]
#check (specializes_iff_mem_closure :
  ∀ {X : Type u} [TopologicalSpace X] {y x : X},
    y ⤳ x ↔ x ∈ closure ({y} : Set X))
