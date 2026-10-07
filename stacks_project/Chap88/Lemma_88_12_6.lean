module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_29_1_TopologicallyOfFiniteType
public import stacks_project.Chap87.Lemma_87_6_2_IsAdic
public import stacks_project.Chap88.Lemma_88_12_1_FiniteTypeReduction

/-!
# Finite type on reductions versus topological finite type for adic Noetherian maps
-/

@[expose] public section

universe u

open TopologicalRing

namespace RingHom

/-- Lemma 88.12.6: Let `φ : A →+* B` be an adic arrow of `WAdm^Noeth`. Then
`φ` satisfies the finite type on reduction condition of Lemma 88.12.1 if and
only if `φ` is topologically of finite type, which is the condition of
Lemma 88.11.1 once adicity is given. -/
@[stacks 0GG6]
theorem isFiniteTypeOnReduction_iff_topologicallyOfFiniteType {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) :
    φ.IsFiniteTypeOnReduction ↔ φ.TopologicallyOfFiniteType :=
  sorry

end RingHom

namespace RingHom.IsFiniteTypeOnReduction

/-- An adic, topologically finite type homomorphism of Noetherian adic rings is
of finite type on reduction. -/
theorem of_isAdicHom_topologicallyOfFiniteType {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
    (φ : A →+* B) (h_adic : φ.IsAdicHom) (h_tft : φ.TopologicallyOfFiniteType) :
    φ.IsFiniteTypeOnReduction :=
  sorry

end RingHom.IsFiniteTypeOnReduction

namespace Algebra.TopologicallyOfFiniteType

/-- For an adic algebra map of Noetherian adic rings, finite type on reduction
is equivalent to the algebra being topologically of finite type. -/
theorem iff_isFiniteTypeOnReduction {R A : Type u}
    [CommRing R] [TopologicalSpace R] [IsAdicRing R] [IsNoetherianRing R]
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [Algebra R A] (h_adic : (algebraMap R A).IsAdicHom) :
    (algebraMap R A).IsFiniteTypeOnReduction ↔ TopologicallyOfFiniteType R A :=
  sorry

end Algebra.TopologicallyOfFiniteType
