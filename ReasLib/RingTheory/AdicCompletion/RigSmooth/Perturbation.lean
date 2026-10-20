module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.AdicCompletion.RigSmooth

/-!
# Perturbations of rig-smooth completed quotient presentations

Sufficiently high-order perturbations of the generators and relations of a
rig-smooth quotient of a completed polynomial ring yield isomorphic algebras.
-/

@[expose] public section

universe u

namespace Algebra.NaiveCotangent.Adic

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
variable {ι κ τ : Type u} [Fintype ι] [Fintype κ] [Fintype τ]

/-- A rig-smooth quotient of an adically completed finite polynomial algebra
is isomorphic as an algebra to every sufficiently high-order perturbation of
its generators and relation matrix whose associated maps form a complex. -/
@[stacks 0GAR]
theorem exists_algEquiv_of_congr_mod_pow
    (g : κ → polynomialCompletion A I ι)
    (K : Matrix κ τ (polynomialCompletion A I ι))
    (hres : Function.Exact (Matrix.mulVecLin K)
      (Fintype.linearCombination (polynomialCompletion A I ι) g))
    [Algebra.RigSmooth I
      (polynomialCompletion A I ι ⧸ Ideal.span (Set.range g))] :
    ∃ n : ℕ, ∀ (g' : κ → polynomialCompletion A I ι)
        (K' : Matrix κ τ (polynomialCompletion A I ι)),
      (∀ i, g i - g' i ∈
        (I.map (algebraMap A (polynomialCompletion A I ι))) ^ n) →
      (∀ i j, (K - K') i j ∈
        (I.map (algebraMap A (polynomialCompletion A I ι))) ^ n) →
      ((Fintype.linearCombination (polynomialCompletion A I ι) g').comp
          (Matrix.mulVecLin K') = 0) →
      Nonempty
        ((polynomialCompletion A I ι ⧸ Ideal.span (Set.range g)) ≃ₐ[A]
          (polynomialCompletion A I ι ⧸ Ideal.span (Set.range g'))) :=
  sorry

end Algebra.NaiveCotangent.Adic
