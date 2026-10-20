/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Ideal.RigClosed

/-!
# Rig-closed primes of Noetherian adic rings

The shared rig-closed-prime API characterizes rig-closedness by primeness,
quotient dimension one, and avoidance of every topological ideal of definition.
-/

@[expose] public section

universe u

variable {A : Type u} [CommRing A] [TopologicalSpace A]
  [TopologicalRing.IsAdicRing A] [IsNoetherianRing A]

#check (Ideal.IsRigClosed.spec :
    ∀ (q : Ideal A), Ideal.IsRigClosed q ↔
      q.IsPrime ∧ ringKrullDim (A ⧸ q) = 1 ∧
        ∀ I : Ideal A, TopologicalRing.Ideal.IsIdealOfDefinition I → ¬ I ≤ q)
