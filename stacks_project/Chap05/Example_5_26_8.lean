/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Topology.Category.Profinite.Basic
public import ReasLib.Topology.Compactification.StoneCech
import StacksCheckRecall

@[expose] public section

universe u

variable {X : Type u} [TopologicalSpace X] [DiscreteTopology X]

/- Example 5.26.8: the Stone-Cech compactification of a discrete space is extremally
disconnected. -/
@[stacks 090C]
#check (inferInstance : ExtremallyDisconnected (StoneCech X))

/- The bundled profinite owner then follows through Mathlib's standard instance chain. -/
#check (Profinite.of (StoneCech X) : Profinite)
