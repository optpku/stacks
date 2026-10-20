/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Sheaves.Points
public import Mathlib.Topology.Sober
public import StacksCheckRecall.CommandCrossRef

@[expose] public section

open CategoryTheory TopCat TopologicalSpace

universe u

namespace CategoryTheory

variable {X : TopCat.{u}}

/- Example 7.33.6 (04EJ) is recorded at the canonical formalization layer:
opens-site points are represented by `GrothendieckTopology.Point`, while the
topological inputs are `IrreducibleCloseds` and, in the sober case,
`irreducibleSetEquivPoints`.  The former Chapter-local construction of a
point from an irreducible closed set was a proof-only DAG and is deliberately
not a competing public owner. -/
@[stacks 04EJ] #check @GrothendieckTopology.Point
#check @IrreducibleCloseds
#check @irreducibleSetEquivPoints
#check @Opens.pointGrothendieckTopology

end CategoryTheory
