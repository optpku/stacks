/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary
import StacksCheckRecall

universe u

/- Definition 29.17.1: a locally Noetherian scheme `S` is universally catenary if every scheme
locally of finite type over `S` is catenary. -/
@[stacks 02J8] #check (AlgebraicGeometry.UniversallyCatenary :
  AlgebraicGeometry.Scheme.{u} → Prop)
