/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Algebra.TensorProduct.PolynomialResolution
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct

universe u v w

/- 37.39.6.1: after base change to a Noetherian `C`-algebra `Rhat`, a finite-type
`C`-algebra `B` admits an exact finite free resolution over a polynomial ring ending in
`B ⊗[C] Rhat`. -/
@[stacks 0CAZ] #check
  (Algebra.TensorProduct.exists_exactPolynomialResolution :
    ∀ {C : Type u} [CommRing C] (B : Type v) (Rhat : Type w)
      [CommRing B] [CommRing Rhat] [Algebra C B] [Algebra C Rhat]
      [Algebra.FiniteType C B] [IsNoetherianRing Rhat],
    ∃ n m K : ℕ, ∃ x : Fin n → B,
      ∃ relationMap :
          (Fin K → MvPolynomial (Fin n) Rhat) →ₗ[MvPolynomial (Fin n) Rhat]
            (Fin m → MvPolynomial (Fin n) Rhat),
        ∃ equationMap :
            (Fin m → MvPolynomial (Fin n) Rhat) →ₗ[MvPolynomial (Fin n) Rhat]
              MvPolynomial (Fin n) Rhat,
          let q : MvPolynomial (Fin n) Rhat →+* B ⊗[C] Rhat :=
            MvPolynomial.eval₂Hom
              (Algebra.TensorProduct.includeRight : Rhat →ₐ[C] B ⊗[C] Rhat).toRingHom
              (fun i ↦ (Algebra.TensorProduct.includeLeft : B →ₐ[C] B ⊗[C] Rhat) (x i))
          Function.Exact relationMap equationMap ∧ Function.Exact equationMap q ∧
            Function.Surjective q)
