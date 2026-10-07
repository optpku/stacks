module

public import Mathlib.RingTheory.Noetherian.Defs
public import stacks_project.Chap88.Lemma_88_3_4_Comparison
public import stacks_project.Chap88.Lemma_88_3_4_Presentation

/-!
# Lemma 88.3.4

A Remark 88.2.3 map of Noetherian pairs induces a canonical comparison of
completed naive cotangent complexes which is an isomorphism on `H^0` and a
surjection on `H^{-1}`.
-/

@[expose] public section

universe u

open Algebra.NaiveCotangent.Adic
open Algebra.TopologicallyFiniteType

namespace Algebra.NaiveCotangent.Adic
open BaseChange

variable {A1 A2 B1 ι : Type u}
variable [CommRing A1] [CommRing A2] [Algebra A1 A2] [CommRing B1] [Algebra A1 B1]
variable [IsNoetherianRing A1] [IsNoetherianRing A2]
variable (I1 : Ideal A1) (I2 : Ideal A2) {c : ℕ} (hc : 1 ≤ c)
variable (hI : I1.map (algebraMap A1 A2) ^ c ≤ I2) (hI2 : I2.FG)
variable [Algebra.TopologicallyFiniteType I1 B1]
variable [Fintype ι]
variable (P : Presentation A1 B1 I1 ι)

/-- Lemma 88.3.4 (1): Let `(A1, I1) → (A2, I2)` be as in Remark 88.2.3 with
`A1` and `A2` Noetherian. Let `B1` be in (88.2.0.2) for `(A1, I1)`, and let
`B2` be the completed base change `(B1 ⊗[A1] A2)^∧`. The canonical chain map
`NL_{B1/A1}^∧ ⊗_{B1} B2 ⟶ NL_{B2/A2}^∧` is an isomorphism on `H^0`. -/
@[stacks 0GAG]
theorem homologyZero_bijective :
    Function.Bijective (homologyZero I1 I2 hc hI hI2 P) := sorry

/-- Lemma 88.3.4 (2): Let `(A1, I1) → (A2, I2)` be as in Remark 88.2.3 with
`A1` and `A2` Noetherian. Let `B1` be in (88.2.0.2) for `(A1, I1)`, and let
`B2` be the completed base change `(B1 ⊗[A1] A2)^∧`. The canonical chain map
`NL_{B1/A1}^∧ ⊗_{B1} B2 ⟶ NL_{B2/A2}^∧` is a surjection on `H^{-1}`. -/
@[stacks 0GAG]
theorem homologyOne_surjective :
    Function.Surjective (homologyOne I1 I2 hc hI hI2 P) := sorry

end Algebra.NaiveCotangent.Adic
