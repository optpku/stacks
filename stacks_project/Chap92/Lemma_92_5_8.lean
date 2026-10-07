module

public import stacks_project.Chap92.«92_7_0_1_Triangle»
public import stacks_project.Chap92.Lemma_92_4_1_PolynomialOver
import Mathlib.Tactic.CrossRefAttribute

/-!
# Transitivity triangle for a polynomial algebra

Lemma 92.5.8 records that the canonical transitivity triangle of cotangent
complexes is distinguished in `D(C)` when the intermediate algebra is polynomial.
-/

@[expose] public section

open Algebra
open CategoryTheory
open CategoryTheory.Pretriangulated

universe u

namespace Algebra.CotangentComplex

/-- Lemma 92.5.8. Let `A → B → C` be ring maps. If `B` is a polynomial algebra over `A`,
then the transitivity triangle `transitivityTriangle A B C` is distinguished in `D(C)`:
`tensor A B C ⟶ derived A C ⟶ derived B C ⟶ (tensor A B C)⟦1⟧`. -/
@[stacks 08SA]
theorem transitivityTriangle_distinguished_of_isPolynomial
    (A B C : Type u) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [IsPolynomial A B] :
    transitivityTriangle A B C ∈ distTriang (DerivedCategory (ModuleCat.{u} C)) :=
  sorry

/-- The transitivity triangle for `A → MvPolynomial σ A → C` is distinguished in `D(C)`. -/
theorem transitivityTriangle_distinguished_of_mvPolynomial
    (A : Type u) (σ : Type u) (C : Type u) [CommRing A] [CommRing C]
    [Algebra (MvPolynomial σ A) C] [Algebra A C]
    [IsScalarTower A (MvPolynomial σ A) C] :
    transitivityTriangle A (MvPolynomial σ A) C ∈
      distTriang (DerivedCategory (ModuleCat.{u} C)) :=
  sorry

end Algebra.CotangentComplex
