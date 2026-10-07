module

public import Mathlib.Data.List.TFAE
public import Mathlib.Tactic.CrossRefAttribute
public import stacks_project.Chap87.Definition_87_5_1_Taut
public import stacks_project.Chap87.Definition_87_29_1_TopologicallyOfFiniteType
public import stacks_project.Chap87.Lemma_87_6_2_IsAdic
public import stacks_project.Chap87.Lemma_87_29_6_RestrictedPowerSeries
public import stacks_project.Chap87.Remark_87_21_4_Variant_for_adic_star_MorphismProperty
public import stacks_project.Chap88.Lemma_88_11_1_Completion
public import stacks_project.Chap88.Lemma_88_11_1_FiniteType

/-!
# Adic topologically finite type arrows of WAdm^{adic*}

A continuous homomorphism of adic rings with a finitely generated ideal of
definition is adic and topologically of finite type if and only if it is taut
and topologically of finite type, equivalently if special-fiber or (88.2.0.2)
conditions hold, equivalently if the target is a closed quotient of a
finite-variable restricted power series algebra or polynomial completion, and
this property is local in the sense of Remark 87.21.4.
-/

@[expose] public section

open TopologicalRing
open TopologicalRing.Ideal

universe u

namespace RingHom

variable {A B : Type u}
variable [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
variable [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]

/-- Lemma 88.11.1 (1): Let `A` and `B` be objects of `WAdm^{adic*}`, and let
`φ : A →+* B` be a continuous ring homomorphism. The following are equivalent:
`φ` is adic and topologically of finite type; `φ` is taut and topologically of
finite type; `φ` is adic and `φ.mapQuotient I'` is of finite type for some
ideal of definition `I'`; for every ideal of definition `I` the topology on `B`
is the `I`-adic topology and `φ.mapQuotient I` is of finite type; for some
ideal of definition `I` the topology on `B` is the `I`-adic topology and `B`
lies in the category (88.2.0.2); the same for every ideal of definition; `B`
is a closed quotient of `RestrictedPowerSeries (Fin n) A`; `B` is a closed
quotient of `IAdicRestrictedPowerSeries (Fin n) I` for some ideal of
definition `I` of `A`. -/
@[stacks 0GBW]
theorem isAdicHom_and_topologicallyOfFiniteType_tfae {φ : A →+* B}
    (hφ : Continuous φ) :
    List.TFAE
      [φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType,
        φ.IsTaut ∧ φ.TopologicallyOfFiniteType,
        φ.IsAdicHom ∧ φ.IsFiniteTypeOnSomeSpecialFiber,
        φ.IsAdicAndFiniteTypeOnEverySpecialFiber,
        φ.IsAdicAndTopologicallyFiniteTypeOnSome,
        φ.IsAdicAndTopologicallyFiniteTypeOnEvery,
        φ.IsClosedQuotientOfRestrictedPowerSeries,
        φ.IsClosedQuotientOfPolynomialCompletion] :=
  sorry

/-- Adic together with topological finite type is equivalent to taut together
with topological finite type. -/
theorem isAdicHom_and_topologicallyOfFiniteType_iff_isTaut_and_topologicallyOfFiniteType
    {φ : A →+* B} (hφ : Continuous φ) :
    (φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) ↔
      φ.IsTaut ∧ φ.TopologicallyOfFiniteType :=
  sorry

/-- Adic together with topological finite type is equivalent to `B` being a
closed quotient of `RestrictedPowerSeries (Fin n) A` as a topological
`A`-algebra. -/
theorem isAdicHom_and_topologicallyOfFiniteType_iff_isClosedQuotientOfRestrictedPowerSeries
    {φ : A →+* B} (hφ : Continuous φ) :
    (φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) ↔
      φ.IsClosedQuotientOfRestrictedPowerSeries :=
  sorry

/-- Adic together with topological finite type is equivalent to `B` being a
closed quotient of a polynomial completion `IAdicRestrictedPowerSeries (Fin n) I`. -/
theorem isAdicHom_and_topologicallyOfFiniteType_iff_isClosedQuotientOfPolynomialCompletion
    {φ : A →+* B} (hφ : Continuous φ) :
    (φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) ↔
      φ.IsClosedQuotientOfPolynomialCompletion :=
  sorry

/-- Adic together with topological finite type is equivalent to the existence of
an ideal of definition inducing the `I`-adic topology with `B` in (88.2.0.2). -/
theorem isAdicHom_and_topologicallyOfFiniteType_iff_isAdicAndTopologicallyFiniteTypeOnSome
    {φ : A →+* B} (hφ : Continuous φ) :
    (φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) ↔
      φ.IsAdicAndTopologicallyFiniteTypeOnSome :=
  sorry

end RingHom

namespace TopologicalRing.IsAdicStarRing

/-- Lemma 88.11.1 (2): The equivalent conditions of Lemma 88.11.1 define a local
property of morphisms of `WAdm^{adic*}` as defined in Formal Spaces,
Remark 87.21.4, recorded as `IsLocalMorphismProperty` of
`fun φ ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType`. -/
@[stacks 0GBW]
theorem isLocalMorphismProperty_isAdicHom_and_topologicallyOfFiniteType :
    IsLocalMorphismProperty
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
        (φ : B →+* A) ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType :=
  sorry

end TopologicalRing.IsAdicStarRing
