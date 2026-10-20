/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.Trace.GroupAlgebra
public import ReasLib.RepresentationTheory.MonoidAlgebra.Restriction

@[expose] public section

open Ring
open scoped MonoidAlgebra Ring
open MonoidAlgebra

noncomputable section

universe u v w x

namespace LinearMap.FiniteProjective

variable {Λ : Type u} {G : Type v} {Γ : Type w}
variable [Ring Λ] [Group G] [Monoid Γ] [Finite G]
variable (S : NatMonoidExtension G Γ) (P : Type x)
variable [AddCommGroup P] [Module (Λ[Γ]) P] [Module (Λ[G]) P] [Module Λ P]
variable [IsScalarTower Λ (Λ[G]) P] [IsScalarTower Λ (Λ[Γ]) P]
variable [Module.Finite (Λ[G]) P] [Module.Projective (Λ[G]) P]
variable [Module.Finite Λ P] [Module.Projective Λ P]
variable [IsRestrictionAlongInl Λ S P]

/-- For a monoid-algebra module finite projective over the kernel-group algebra,
the coefficient-ring trace of a monoid element is the cardinality of its
kernel-group centralizer times the trace over that centralizer algebra. -/
theorem traceNatural_smulEnd_eq_card_centralizer_smul_traceG (γ : Γ) :
    (traceNatural (smulEnd γ : Module.End Λ P) : Λ♮) =
      Nat.card (S.centralizer γ) •
        traceG (smulEndZ S γ : Module.End (Λ[S.centralizer γ]) P) :=
  sorry

end LinearMap.FiniteProjective
