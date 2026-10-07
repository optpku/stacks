module

public import Mathlib.RingTheory.Noetherian.Defs
public import ReasLib.RingTheory.CompleteIntersection.Local.RingHom
public import stacks_project.Chap88.«88_2_0_2_TopologicallyFiniteType»
public import stacks_project.Chap88.«88_2_0_3_QuotientSystem»
public import stacks_project.Chap88.Lemma_88_3_5_ExactSequence

/-!
# Lemma 88.3.6

Stagewise local complete intersection of `B ⧸ I^n B → C ⧸ I^n C` implies
injectivity of the Jacobi–Zariski map
`H^{-1}(NL_{B/A}^∧ ⊗[B] C) ⟶ H^{-1}(NL_{C/A}^∧)`.
-/

@[expose] public section

universe u

open Algebra.NaiveCotangent.Adic

namespace Algebra.NaiveCotangent.Adic

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [IsNoetherianRing A]
variable [Algebra A B] [Algebra A C] [Algebra B C] [IsScalarTower A B C]
variable (I : Ideal A) [Algebra.TopologicallyFiniteType I B]
  [Algebra.TopologicallyFiniteType I C]
variable {ι κ : Type u} [Fintype ι] [Fintype κ]
variable (P : Presentation A B I ι)
variable (Q : Presentation B C (I.map (algebraMap A B)) κ)

/-- Lemma 88.3.6: with assumptions as in Lemma 88.3.5, if each stage map
`B ⧸ I^n B → C ⧸ I^n C` is a local complete intersection homomorphism, then
`H^{-1}(NL_{B/A}^∧ ⊗[B] C) ⟶ H^{-1}(NL_{C/A}^∧)` is injective. -/
@[stacks 0AQJ]
theorem homologyOneTensor_injective
    (h_lci : ∀ n : ℕ+,
      (CommAlgCat.adicQuotientMap I (IsScalarTower.toAlgHom A B C) n).IsLocalCompleteIntersection) :
    Function.Injective (homologyOneTensor I P Q) := sorry

end Algebra.NaiveCotangent.Adic
