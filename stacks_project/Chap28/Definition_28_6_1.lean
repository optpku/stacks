/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Topology.JacobsonSpace
import StacksCheckRecall

@[expose] public section

universe u

namespace AlgebraicGeometry

variable (S : Scheme.{u})

/- Definition 28.6.1: a scheme `S` is Jacobson if its underlying topological space is Jacobson.
In this project that source-facing notion is exactly the canonical owner `JacobsonSpace S`, so
this item is recorded as a check-only bridge. -/
@[stacks 01P2] #check (JacobsonSpace S : Prop)

end AlgebraicGeometry
