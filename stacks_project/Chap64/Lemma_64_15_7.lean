module

public import stacks_project.Chap64.Definition_64_15_2_Trace
public import stacks_project.Chap64.Lemma_64_15_9_Extension
import Mathlib.Tactic.CrossRefAttribute

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

/-- Lemma 64.15.7. Let `P` be a `Λ[Γ]`-module, finite and projective as a
`Λ[G]`-module, and `γ ∈ Γ`. Then `Tr_Λ(γ, P)` equals
`#Z_γ · Tr_Λ^{Z_γ}(γ, P)`: the finite-projective trace
`traceNatural (smulEnd γ)` in `Λ♮` equals
`Nat.card (S.centralizer γ) • traceG (smulEndZ S γ)`. -/
@[stacks 03UB]
theorem traceNatural_smulEnd_eq_card_centralizer_smul_traceG (γ : Γ) :
    (traceNatural (smulEnd γ : Module.End Λ P) : Λ♮) =
      Nat.card (S.centralizer γ) •
        traceG (smulEndZ S γ : Module.End (Λ[S.centralizer γ]) P) :=
  sorry

end LinearMap.FiniteProjective
