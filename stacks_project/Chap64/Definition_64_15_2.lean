/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.Trace.GroupAlgebra
import StacksCheckRecall

universe u v w

open scoped MonoidAlgebra Ring

/- Definition 64.15.2: for an endomorphism f of a finite projective left Λ[G]-module P,
the G-trace is Tr_Λ^G(f; P) := ε(Tr_{Λ[G]}(f; P)) in Λ♮, where ε : (Λ[G])♮ → Λ♮ is
induced by the identity-coefficient map. -/
@[stacks 03U6] #check (LinearMap.FiniteProjective.traceG :
    ∀ {Λ : Type u} {G : Type v} [Ring Λ] [Group G] [Finite G]
    {P : Type w} [AddCommGroup P] [Module (Λ[G]) P]
    [Module.Finite (Λ[G]) P] [Module.Projective (Λ[G]) P],
    Module.End (Λ[G]) P →+ Λ♮)
