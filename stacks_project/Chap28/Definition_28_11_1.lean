/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme
public import ReasLib.Topology.Catenary
import StacksCheckRecall

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

namespace AlgebraicGeometry

universe u

variable (S : Scheme.{u})

/- Definition 28.11.1: A scheme is catenary when its underlying topological space is catenary. -/
@[stacks 02IW] #check (TopologicalSpace.CatenarySpace S : Prop)

end AlgebraicGeometry
