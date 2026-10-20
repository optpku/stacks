module

public import ReasLib.LinearAlgebra.Trace.GroupAlgebra.Centralizer
import StacksCheckRecall

@[expose] public section

open scoped MonoidAlgebra Ring

universe u v w x

/- Lemma 64.15.7. Let `P` be a `Λ[Γ]`-module, finite and projective as a
`Λ[G]`-module, and `γ ∈ Γ`. Then `Tr_Λ(γ, P)` equals
`#Z_γ · Tr_Λ^{Z_γ}(γ, P)`: the finite-projective trace
`traceNatural (smulEnd γ)` in `Λ♮` equals
`Nat.card (S.centralizer γ) • traceG (smulEndZ S γ)`. -/
@[stacks 03UB] #check
  (LinearMap.FiniteProjective.traceNatural_smulEnd_eq_card_centralizer_smul_traceG :
    ∀ {Λ : Type u} {G : Type v} {Γ : Type w}
      [Ring Λ] [Group G] [Monoid Γ] [Finite G]
      (S : NatMonoidExtension G Γ) (P : Type x)
      [AddCommGroup P] [Module (Λ[Γ]) P] [Module (Λ[G]) P] [Module Λ P]
      [IsScalarTower Λ (Λ[G]) P] [IsScalarTower Λ (Λ[Γ]) P]
      [Module.Finite (Λ[G]) P] [Module.Projective (Λ[G]) P]
      [Module.Finite Λ P] [Module.Projective Λ P]
      [MonoidAlgebra.IsRestrictionAlongInl Λ S P] (γ : Γ),
    (LinearMap.FiniteProjective.traceNatural
      (LinearMap.FiniteProjective.smulEnd γ : Module.End Λ P) : Λ♮) =
      Nat.card (S.centralizer γ) •
        LinearMap.FiniteProjective.traceG
          (LinearMap.FiniteProjective.smulEndZ S γ : Module.End (Λ[S.centralizer γ]) P))
