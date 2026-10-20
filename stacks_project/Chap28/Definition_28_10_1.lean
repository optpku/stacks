/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.Topology.KrullDimension.Local
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

section

variable (X : Scheme.{u}) (x : X)

/- Definition 28.10.1: for a scheme `X`, the dimension of `X` is the topological Krull dimension
of its underlying topological space, and the dimension at a point `x : X` is the local
topological Krull dimension `topologicalKrullDimAt x`. -/
@[stacks 04MT] #check (topologicalKrullDim X : WithBot ℕ∞)
#check (topologicalKrullDimAt x : WithBot ℕ∞)

end

end AlgebraicGeometry
