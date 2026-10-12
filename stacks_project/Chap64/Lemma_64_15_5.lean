/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.Algebra.Module.TensorProduct.Diagonal
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u v w p m

open scoped MonoidAlgebra TensorProduct

variable (A : Type u) (Λ : Type v) (G : Type w) (P : Type p) (M : Type m)
variable [CommRing A] [Ring Λ] [Algebra A Λ] [Group G] [Finite G]
variable [AddCommGroup P] [Module A P]
variable [AddCommGroup M] [Module A M] [Module Λ M] [IsScalarTower A Λ M]
variable [Module (A[G]) P] [IsScalarTower A (A[G]) P]
variable [Module (Λ[G]) M] [IsScalarTower Λ (Λ[G]) M]
variable [Module.Finite (A[G]) P] [Module.Projective (A[G]) P]
variable [Module.Finite Λ M] [Module.Projective Λ M]

/- Lemma 64.15.5 (1): if `P` is a finite projective `A[G]`-module and `M` a
`Λ[G]`-module finite projective over `Λ`, then the diagonal tensor is finite
over `Λ[G]`. -/
@[stacks 03U9] #check (TensorProduct.Diagonal.instFinite
  (A := A) (Λ := Λ) (G := G) (P := P) (M := M) :
  Module.Finite (Λ[G]) (TensorProduct.Diagonal A Λ G P M))

/- Lemma 64.15.5 (2): under the same hypotheses, the diagonal tensor is
projective over `Λ[G]`. -/
@[stacks 03U9] #check (TensorProduct.Diagonal.instProjective
  (A := A) (Λ := Λ) (G := G) (P := P) (M := M) :
  Module.Projective (Λ[G]) (TensorProduct.Diagonal A Λ G P M))
