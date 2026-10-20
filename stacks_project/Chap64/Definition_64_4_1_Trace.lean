/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.Trace.CommutatorQuotient

universe u v

variable (R : Type u) [Ring R] (n : Type v) [Fintype n] [DecidableEq n]

#check (LinearMap.traceNatural : Module.End R (n → R) →+ Ring.CommutatorQuotient R)
