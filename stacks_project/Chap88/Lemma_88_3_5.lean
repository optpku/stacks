/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Noetherian.Defs
public import stacks_project.Chap88.«88_2_0_2_TopologicallyFiniteType»
public import stacks_project.Chap88.Lemma_88_3_5_Instances
public import stacks_project.Chap88.Lemma_88_3_5_Presentation
public import stacks_project.Chap88.Lemma_88_3_5_ExactSequence

/-!
# Lemma 88.3.5

The completed naive cotangent complexes of a tower of objects of (88.2.0.2)
fit into a six-term Jacobi–Zariski exact sequence.
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

/-- Lemma 88.3.5 (1): exactness of the six-term sequence at
`H^{-1}(NL_{C/B}^∧)`. -/
@[stacks 0ALM]
theorem exact_map_δ :
    Function.Exact (homologyOneMap I P Q) (δ I P Q) := sorry

/-- Lemma 88.3.5 (2): exactness of the six-term sequence at
`C ⊗_B H^0(NL_{B/A}^∧)`. -/
@[stacks 0ALM]
theorem exact_δ_homologyZeroBaseChange :
    Function.Exact (δ I P Q) (homologyZeroBaseChange I P Q) := sorry

/-- Lemma 88.3.5 (3): exactness of the six-term sequence at
`H^0(NL_{C/A}^∧)`. -/
@[stacks 0ALM]
theorem exact_homologyZeroBaseChange_map :
    Function.Exact (homologyZeroBaseChange I P Q) (homologyZeroMap I P Q) := sorry

/-- Lemma 88.3.5 (4): the terminal map `H^0(NL_{C/A}^∧) ⟶ H^0(NL_{C/B}^∧)` is
surjective. -/
@[stacks 0ALM]
theorem homologyZeroMap_surjective :
    Function.Surjective (homologyZeroMap I P Q) := sorry

/-- Lemma 88.3.5 (5): exactness of the six-term sequence at
`H^{-1}(NL_{C/A}^∧)`. -/
@[stacks 0ALM]
theorem exact_homologyOneTensor_map :
    Function.Exact (homologyOneTensor I P Q) (homologyOneMap I P Q) := sorry

end Algebra.NaiveCotangent.Adic
