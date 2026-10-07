module

public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap88.«88_2_0_2_TopologicallyFiniteType»
public import stacks_project.Chap88.Lemma_88_4_2_Jacobian

/-!
# Algebraization of an elementary Jacobian presentation

A topologically finite type algebra over a Noetherian pair that admits a
completed presentation with a single elementary Jacobian element covering
`V(I B)` is isomorphic to the `I`-adic completion of a finite type algebra.
-/

@[expose] public section

universe u

open PrimeSpectrum
open scoped PrimeSpectrum
open Algebra.NaiveCotangent.Adic

namespace Algebra.NaiveCotangent.Adic
open Presentation

/-- Lemma 88.7.2: Let `I` be an ideal of a Noetherian ring `A`. Let `B` be an
object of (88.2.0.2). Let `B = A[x_ι]^∧ / J` be a presentation. Assume there
exists an element `b ∈ B`, relations `f₁, …, fₘ ∈ J`, and columns such that
`V({b}) ⊆ V(I B)` in `Spec(B)`, the image of `Δ = jacobianMinor P fs cols` in
`B` divides `b`, and `relationCondition P b fs`. Then there exists a finite
type `A`-algebra `C` and an `A`-algebra isomorphism `B ≅ C^∧`. -/
@[stacks 0GAW]
theorem exists_finiteTypeAlgEquiv_of_elementaryJacobian
    {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [Algebra A B]
    (I : Ideal A) [Algebra.TopologicallyFiniteType I B] {ι : Type u}
    (P : Presentation A B I ι) {m : ℕ} (b : B) (fs : Fin m → P.ker)
    (cols : Fin m ↪ ι) (hV : V({b}) ⊆ V((I.map (algebraMap A B) : Set B)))
    (hΔ : jacobianMinor P fs cols ∣ b) (hrel : relationCondition P b fs) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C)
      (_ : Algebra.FiniteType A C),
      Nonempty (AdicCompletion (I.map (algebraMap A C)) C ≃ₐ[A] B) :=
  sorry

end Algebra.NaiveCotangent.Adic
