/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.LinearAlgebra.Trace.GroupAlgebra.TensorProduct
import StacksCheckRecall

@[expose] public section

open Ring LinearMap.FiniteProjective TensorProduct
open scoped MonoidAlgebra TensorProduct Ring

noncomputable section

universe u v w p m

namespace LinearMap.FiniteProjective

variable {A : Type u} {Λ : Type v} {G : Type w} {P : Type p} {M : Type m}
variable [CommRing A] [Ring Λ] [Algebra A Λ] [Group G] [Finite G]
variable [AddCommGroup P] [Module A P] [Module (A[G]) P] [IsScalarTower A (A[G]) P]
variable [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
variable [Module (Λ[G]) M] [IsScalarTower Λ (Λ[G]) M]
variable [Module.Finite (A[G]) P] [Module.Projective (A[G]) P]
variable [Module.Finite Λ M] [Module.Projective Λ M]

/- Lemma 64.15.6. With assumptions as in Lemma 64.15.5, let `u` be an
endomorphism of the finite projective `A[G]`-module `P` and `v` an
endomorphism of the `Λ[G]`-module `M`. Then the G-trace of the mixed-ring
tensor `u ⊗ v` on the diagonal tensor `P ⊗[A] M` equals the product
`Tr_A^G(u; P) · Tr_Λ(v; M)` in `Λ♮`, where the product is the `A`-module
action on `Λ♮` after the identification `A♮ ≃+ A`. -/
@[stacks 03UA] #check (LinearMap.FiniteProjective.traceG_tmulEnd :
  ∀ (u : Module.End (A[G]) P) (v : Module.End (Λ[G]) M),
    traceG (Diagonal.tmulEnd A Λ G P M u v) =
      CommutatorQuotient.mkAddEquiv.symm (traceG u) •
        (traceNatural (v.restrictScalars Λ) : Λ♮))

/- If `Tr_A^G(u; P)` is the class of `a` in `A♮`, then the mixed-ring identity
specializes to `Tr_Λ^G(u ⊗ v) = a • Tr_Λ(v; M)`. -/
#check (LinearMap.FiniteProjective.traceG_tmulEnd_mk :
  ∀ (u : Module.End (A[G]) P) (v : Module.End (Λ[G]) M) (a : A)
    (ha : CommutatorQuotient.mk a = traceG u),
    traceG (Diagonal.tmulEnd A Λ G P M u v) =
      a • traceNatural (v.restrictScalars Λ))

end LinearMap.FiniteProjective
