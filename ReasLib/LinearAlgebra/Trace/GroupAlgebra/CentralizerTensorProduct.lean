module

public import ReasLib.LinearAlgebra.Trace.GroupAlgebra.TensorProduct
public import ReasLib.RepresentationTheory.MonoidAlgebra.Restriction

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

/-- For compatible modules over a natural-number monoid extension, with `P`
finite projective over `A[G]` and `M` finite projective over `Λ`, the centralizer
trace of the diagonal action on `P ⊗[A] M` is the centralizer trace on `P`
acting on the ordinary trace on `M`. The scalar action uses the identification
`A♮ ≃+ A`, and `Λ` need not be commutative. -/
theorem traceG_tmulEnd_smulEndZ (γ : Γ) :
    traceG (Diagonal.tmulEnd A Λ (S.centralizer γ) P M
        (smulEndZ S γ : Module.End (A[S.centralizer γ]) P)
        (smulEndZ S γ : Module.End (Λ[S.centralizer γ]) M)) =
      CommutatorQuotient.mkAddEquiv.symm
          (traceG (smulEndZ S γ : Module.End (A[S.centralizer γ]) P)) •
        (traceNatural (smulEnd γ : Module.End Λ M) : Λ♮) :=
  sorry

/-- If the centralizer trace of the monoid action on `P` is represented by
`a : A`, then the centralizer trace of the diagonal action on `P ⊗[A] M`
equals `a` acting on the ordinary trace of the monoid action on `M`. -/
theorem traceG_tmulEnd_smulEndZ_mk (γ : Γ)
    (a : A)
    (ha : CommutatorQuotient.mk a =
      traceG (smulEndZ S γ : Module.End (A[S.centralizer γ]) P)) :
    traceG (Diagonal.tmulEnd A Λ (S.centralizer γ) P M
        (smulEndZ S γ : Module.End (A[S.centralizer γ]) P)
        (smulEndZ S γ : Module.End (Λ[S.centralizer γ]) M)) =
      a • traceNatural (smulEnd γ : Module.End Λ M) :=
  sorry

end LinearMap.FiniteProjective
