module

public import stacks_project.Chap64.Definition_64_15_2_Trace
public import stacks_project.Chap64.Lemma_64_15_4_Module
public import stacks_project.Chap64.Lemma_64_15_6_MkAddEquiv
public import stacks_project.Chap64.Lemma_64_15_6_TmulEnd
public import stacks_project.Chap64.Lemma_64_15_9_Extension
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open Ring LinearMap.FiniteProjective TensorProduct
open scoped MonoidAlgebra TensorProduct Ring
open MonoidAlgebra

noncomputable section

universe u v w x p m

namespace LinearMap.FiniteProjective

variable {A : Type u} {Λ : Type v} {G : Type w} {Γ : Type x} {P : Type p} {M : Type m}
variable [CommRing A] [Ring Λ] [Algebra A Λ] [Group G] [Monoid Γ] [Finite G]
variable (S : NatMonoidExtension G Γ)
variable [AddCommGroup P] [Module A P] [Module (A[G]) P] [Module (A[Γ]) P]
variable [IsScalarTower A (A[G]) P] [IsScalarTower A (A[Γ]) P]
variable [Module.Finite (A[G]) P] [Module.Projective (A[G]) P]
variable [IsRestrictionAlongInl A S P]
variable [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
variable [Module (Λ[G]) M] [Module (Λ[Γ]) M]
variable [IsScalarTower Λ (Λ[G]) M] [IsScalarTower Λ (Λ[Γ]) M]
variable [Module.Finite Λ M] [Module.Projective Λ M]
variable [IsRestrictionAlongInl Λ S M]

/-- Lemma 64.15.8. Let `P` be an `A[Γ]`-module, finite projective as an
`A[G]`-module, and let `M` be a `Λ[Γ]`-module, finite projective as a
`Λ`-module. Then the `Z_γ`-trace of the diagonal `γ`-action on `P ⊗[A] M`
equals the product `Tr_A^{Z_γ}(γ, P) · Tr_Λ(γ, M)` in `Λ♮`, where the
product is the `A`-module action on `Λ♮` after the identification
`A♮ ≃+ A`. -/
@[stacks 03UC]
theorem traceG_tmulEnd_smulEndZ (γ : Γ)
    [IsScalarTower A (A[S.centralizer γ]) P]
    [IsScalarTower Λ (Λ[S.centralizer γ]) M] :
    traceG (Diagonal.tmulEnd A Λ (S.centralizer γ) P M
        (smulEndZ S γ : Module.End (A[S.centralizer γ]) P)
        (smulEndZ S γ : Module.End (Λ[S.centralizer γ]) M)) =
      CommutatorQuotient.mkAddEquiv.symm
          (traceG (smulEndZ S γ : Module.End (A[S.centralizer γ]) P)) •
        (traceNatural (smulEnd γ : Module.End Λ M) : Λ♮) :=
  sorry

/-- If `Tr_A^{Z_γ}(γ, P)` is the class of `a` in `A♮`, then the mixed-ring
identity specializes to `Tr_Λ^{Z_γ}(γ, P ⊗[A] M) = a • Tr_Λ(γ, M)`. -/
theorem traceG_tmulEnd_smulEndZ_mk (γ : Γ)
    [IsScalarTower A (A[S.centralizer γ]) P]
    [IsScalarTower Λ (Λ[S.centralizer γ]) M]
    (a : A)
    (ha : CommutatorQuotient.mk a =
      traceG (smulEndZ S γ : Module.End (A[S.centralizer γ]) P)) :
    traceG (Diagonal.tmulEnd A Λ (S.centralizer γ) P M
        (smulEndZ S γ : Module.End (A[S.centralizer γ]) P)
        (smulEndZ S γ : Module.End (Λ[S.centralizer γ]) M)) =
      a • traceNatural (smulEnd γ : Module.End Λ M) :=
  sorry

end LinearMap.FiniteProjective
