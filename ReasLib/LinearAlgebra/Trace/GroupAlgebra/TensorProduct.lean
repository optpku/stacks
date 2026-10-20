/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Ring.CommutatorQuotient.Equiv
public import ReasLib.Algebra.Module.TensorProduct.Diagonal.End
public import ReasLib.LinearAlgebra.Trace.GroupAlgebra

/-!
# G-traces of mixed-ring tensor endomorphisms
-/

@[expose] public section

open Ring TensorProduct
open scoped MonoidAlgebra TensorProduct Ring

noncomputable section

universe u v w p m

namespace LinearMap.FiniteProjective

variable {A : Type u} {Λ : Type v} {G : Type w} {P : Type p} {M : Type m}
variable [CommRing A] [Ring Λ] [Algebra A Λ] [Group G]
variable [AddCommGroup P] [Module A P] [Module (A[G]) P] [IsScalarTower A (A[G]) P]
variable [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
variable [Module (Λ[G]) M] [IsScalarTower Λ (Λ[G]) M]
variable [Module.Finite (A[G]) P] [Module.Projective (A[G]) P]
variable [Module.Finite Λ M] [Module.Projective Λ M]

/-- For a finite group, the G-trace of the mixed-ring tensor of endomorphisms
of a finite projective `A[G]`-module and a `Λ[G]`-module finite projective over
`Λ` is the scalar action of the first G-trace on the second ordinary trace. -/
theorem traceG_tmulEnd [Finite G] (u : Module.End (A[G]) P) (v : Module.End (Λ[G]) M) :
    traceG (Diagonal.tmulEnd A Λ G P M u v) =
      CommutatorQuotient.mkAddEquiv.symm (traceG u) •
        (traceNatural (v.restrictScalars Λ) : Λ♮) := sorry

/-- For a finite group, if the G-trace of `u` is represented by `a`, then the
G-trace of its mixed-ring tensor with `v` is `a` times the ordinary trace of `v`. -/
theorem traceG_tmulEnd_mk [Finite G] (u : Module.End (A[G]) P) (v : Module.End (Λ[G]) M)
    (a : A) (ha : CommutatorQuotient.mk a = traceG u) :
    traceG (Diagonal.tmulEnd A Λ G P M u v) =
      a • traceNatural (v.restrictScalars Λ) := sorry

end LinearMap.FiniteProjective
