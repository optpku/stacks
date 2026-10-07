module

public import stacks_project.Chap92.Lemma_92_6_4_Product
import Mathlib.Tactic.CrossRefAttribute

/-!
# Product of cotangent complexes

The comparison `L_{B × C / A} ⟶ L_{B/A} ⊕ L_{C/A}` is an isomorphism in `D(B × C)`.
-/

@[expose] public section

open CategoryTheory

universe u

namespace Algebra.CotangentComplex

/-- Lemma 92.6.4. Let `A → B` and `A → C` be ring maps. Then the map
`L_{B × C / A} ⟶ L_{B/A} ⊕ L_{C/A}` is an isomorphism in `D(B × C)`. -/
@[stacks 08SC]
theorem prodMap_isIso {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : A →+* C) : IsIso (prodMap f g) :=
  sorry

end Algebra.CotangentComplex
