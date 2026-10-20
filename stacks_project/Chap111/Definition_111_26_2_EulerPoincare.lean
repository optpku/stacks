/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Module.EulerPoincare

/-!
# Euler-Poincaré functions

An Euler-Poincaré function on finite `A`-modules is an additive integer invariant of short exact
sequences. The Grothendieck group `K'_0(A)` already quotients by those relations, so the owner is
an additive map `K'_0(A) →+ ℤ`. Competing invariants (length, rank, …) remain explicit parameters.
-/

@[expose] public section

universe u v

#check (Module.EulerPoincareFunction.{u, v} :
  (A : Type u) → [CommRing A] → Type (max u (v + 1)))
