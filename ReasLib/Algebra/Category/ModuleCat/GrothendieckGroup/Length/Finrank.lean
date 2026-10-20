/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import ReasLib.Algebra.Category.ModuleCat.GrothendieckGroup.Length
public import ReasLib.Algebra.Module.EulerPoincare

/-!
# Finite-length Euler-Poincaré values over a field

The composition-length functional on the finite-module Grothendieck group evaluates
on a finite-dimensional vector space as its dimension.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace Module.EulerPoincareFunction

/-- Over a field, the finite-length Euler-Poincaré function evaluates as vector-space
dimension. -/
theorem eval_eq_finrank (k : Type u) [Field k] (M : Type v)
    [AddCommGroup M] [Module k M] [Module.Finite k M] :
    eval (ModuleCat.K0.finiteLength k) M = Module.finrank k M := sorry

end Module.EulerPoincareFunction
