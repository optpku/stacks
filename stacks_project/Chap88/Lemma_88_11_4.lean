module

public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Remark_87_21_13_Variant_for_adic_star_Composition
public import stacks_project.Chap87.Lemma_87_6_2_IsAdic
public import stacks_project.Chap87.Definition_87_29_1_TopologicallyOfFiniteType

/-!
# Adic topologically finite type arrows of WAdm^{adic*} are stable under composition
-/

@[expose] public section

universe u

open TopologicalRing RingHom

namespace TopologicalRing.IsAdicStarRing

/-- Lemma 88.11.4: Consider the property `P` on arrows of `WAdm^{adic*}` defined
in Lemma 88.11.1. Then `P` is stable under composition as defined in Formal
Spaces, Remark 87.21.13. -/
@[stacks 0GBZ]
theorem isStableUnderComposition_isAdicHom_and_topologicallyOfFiniteType :
    IsStableUnderComposition
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
        (φ : B →+* A) ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType :=
  sorry

end TopologicalRing.IsAdicStarRing

namespace RingHom

variable {A B C : Type u}
variable [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
variable [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
variable [CommRing C] [TopologicalSpace C] [IsAdicStarRing C]

/-- Adic and topologically of finite type maps of `WAdm^{adic*}` are preserved
by composition of continuous ring homomorphisms. -/
theorem isAdicHom_and_topologicallyOfFiniteType_comp {φ : B →+* A} {ψ : C →+* B}
    (hφcont : Continuous φ) (hψcont : Continuous ψ)
    (hφ : φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType)
    (hψ : ψ.IsAdicHom ∧ ψ.TopologicallyOfFiniteType) :
    (φ.comp ψ).IsAdicHom ∧ (φ.comp ψ).TopologicallyOfFiniteType :=
  sorry

end RingHom
