/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
import ReasLib.Topology.Sober.GenericPoint

universe u

open Set TopologicalSpace

variable {X : Type u} [TopologicalSpace X] [IrreducibleSpace X]

/- Definition 111.6.12: a point `x` of an irreducible topological space `X` is a generic
point of `X` when `X` equals `closure {x}`; this is Mathlib's `IsGenericPoint` at
`Set.univ`, characterized by `isGenericPoint_def`. -/
@[stacks 027E] #check (fun x : X ↦ isGenericPoint_def (x := x) (S := Set.univ) :
  ∀ x : X, IsGenericPoint x Set.univ ↔ closure ({x} : Set X) = Set.univ)
