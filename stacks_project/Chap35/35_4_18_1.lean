/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicTopology.CosimplicialObject.LowDegree
import StacksCheckRecall

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]
variable (S : CosimplicialObject C)

/- 35.4.18.1: with `S₁ = S^[0]`, `S₂ = S^[1]`, and `S₃ = S^[2]`, the displayed
diagram is the fork whose maps are the three indicated cosimplicial cofaces. -/
@[stacks 08X4] #check
  (CategoryTheory.CosimplicialObject.lowDegreeFork S :
    CategoryTheory.Limits.Fork (S.δ (2 : Fin 3)) (S.δ (1 : Fin 3)))
