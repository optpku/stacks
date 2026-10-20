/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.Trace.Coinvariants

/-!
# Natural-number monoid extensions and their centralizer traces

The shared extension, scalar-restriction, and trace owners provide the extension API.
-/

universe u v w x

open Ring
open scoped MonoidAlgebra Ring

#check (NatMonoidExtension :
    ∀ (G : Type v) (Γ : Type w) [Group G] [Monoid Γ], Type (max v w))

#check (NatMonoidExtension.ofGroupExtension :
    ∀ {G : Type v} [Group G] {E : Type w} [Group E]
    (T : GroupExtension G E (Multiplicative ℤ)),
    NatMonoidExtension G (NatMonoidExtension.nonneg T))

#check (LinearMap.FiniteProjective.conjClassTrace :
    ∀ {Λ : Type u} {G : Type v} {Γ : Type w}
    [Ring Λ] [Group G] [Monoid Γ] [Finite G] (S : NatMonoidExtension G Γ) (P : Type x)
    [AddCommGroup P] [Module (Λ[Γ]) P] [Module (Λ[G]) P] [Module Λ P]
    [Module.Finite (Λ[G]) P] [Module.Projective (Λ[G]) P]
    [IsScalarTower Λ (Λ[G]) P] [IsScalarTower Λ (Λ[Γ]) P]
    [MonoidAlgebra.IsRestrictionAlongInl Λ S P], S.DegreeOneGConjClass → Λ♮)
