module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Polynomial Resolutions after Base Change

This file records a finite free polynomial resolution of a finite-type algebra after base change
to a Noetherian coefficient ring.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Algebra.TensorProduct

/-- If `B` is a finite-type `C`-algebra and `Rhat` is a Noetherian `C`-algebra, then
`B ⊗[C] Rhat` is the quotient of a polynomial algebra over `Rhat` through two finite-rank
free relation stages. -/
theorem exists_exactPolynomialResolution
    {C : Type u} [CommRing C] (B : Type v) (Rhat : Type w)
    [CommRing B] [CommRing Rhat] [Algebra C B] [Algebra C Rhat]
    [Algebra.FiniteType C B] [IsNoetherianRing Rhat] :
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
            Function.Surjective q := sorry

end Algebra.TensorProduct
