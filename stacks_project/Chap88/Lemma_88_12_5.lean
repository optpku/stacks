module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_29_1_TopologicallyOfFiniteType
public import stacks_project.Chap88.Lemma_88_12_1_FiniteTypeReduction

/-!
# Finite type on reductions implies topological finite type for Noetherian adic rings
-/

@[expose] public section

universe u

open TopologicalRing

namespace RingHom

/-- Lemma 88.12.5: Let `φ : A →+* B` be an arrow of `WAdm^Noeth` satisfying
the condition of Lemma 88.12.1. Then `φ` is topologically of finite type. -/
@[stacks 0GC6]
theorem topologicallyOfFiniteType_of_isFiniteTypeOnReduction {A B : Type u}
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [CommRing B] [TopologicalSpace B] [IsAdicRing B] [IsNoetherianRing B]
    (φ : A →+* B) (hφ : Continuous φ) (h : φ.IsFiniteTypeOnReduction) :
    φ.TopologicallyOfFiniteType :=
  sorry

end RingHom

namespace Algebra.TopologicallyOfFiniteType

/-- A continuous algebra map of Noetherian adic rings that is of finite type on
reduction makes the target topologically of finite type. -/
theorem of_isFiniteTypeOnReduction {R A : Type u}
    [CommRing R] [TopologicalSpace R] [IsAdicRing R] [IsNoetherianRing R]
    [CommRing A] [TopologicalSpace A] [IsAdicRing A] [IsNoetherianRing A]
    [Algebra R A] (hφ : Continuous (algebraMap R A))
    (h : (algebraMap R A).IsFiniteTypeOnReduction) :
    TopologicallyOfFiniteType R A :=
  sorry

end Algebra.TopologicallyOfFiniteType
