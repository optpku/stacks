module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import stacks_project.Chap87.Definition_87_4_8_WeaklyAdmissible
public import stacks_project.Chap87.Lemma_87_4_10_TopologicalNilradical

/-!
# Finite type on reductions of weakly admissible rings

A homomorphism of weakly admissible rings is of finite type on reduction when
the induced map on quotients by topological nilradicals is of finite type.
-/

@[expose] public section

universe u

open TopologicalRing

namespace RingHom

variable {A B : Type u} [CommRing A] [TopologicalSpace A] [IsWeaklyAdmissibleRing A]
  [CommRing B] [TopologicalSpace B] [IsWeaklyAdmissibleRing B]

/-- The homomorphism `φ : A →+* B` of weakly admissible rings is of finite type
on reduction when the induced map
`A ⧸ topologicalNilradical A →+* B ⧸ topologicalNilradical B` is of finite
type. -/
def IsFiniteTypeOnReduction (φ : A →+* B) : Prop :=
  ∃ h : topologicalNilradical A ≤ (topologicalNilradical B).comap φ,
    (Ideal.quotientMap (topologicalNilradical B) φ h).FiniteType

/-- For a continuous homomorphism of weakly admissible rings, finite type on
reduction is equivalent to finite type of the induced map on topological
nilradical quotients. -/
theorem isFiniteTypeOnReduction_iff (φ : A →+* B) (hφ : Continuous φ) :
    φ.IsFiniteTypeOnReduction ↔
      (Ideal.quotientMap (topologicalNilradical B) φ
        (topologicalNilradical.map_le φ hφ)).FiniteType :=
  sorry

namespace IsFiniteTypeOnReduction

/-- Finite type on reduction yields finite type of the induced nilradical
quotient map for any nilradical mapping inequality. -/
theorem finiteType {φ : A →+* B} (h : φ.IsFiniteTypeOnReduction)
    (h_le : topologicalNilradical A ≤ (topologicalNilradical B).comap φ) :
    (Ideal.quotientMap (topologicalNilradical B) φ h_le).FiniteType :=
  sorry

end IsFiniteTypeOnReduction

end RingHom
