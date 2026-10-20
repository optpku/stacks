/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import ReasLib.Topology.Algebra.Ring.Taut
public import ReasLib.RingTheory.Topology.FiniteType
public import ReasLib.RingTheory.Topology.Adic.Hom
public import ReasLib.RingTheory.RestrictedPowerSeries.Quotient
public import ReasLib.RingTheory.Topology.AdicStar.LocalMorphismProperty
public import ReasLib.RingTheory.AdicCompletion.PolynomialQuotient
public import ReasLib.RingTheory.Topology.FiniteType.SpecialFiber

/-!
# Adic topologically finite type arrows of WAdm^{adic*}

A continuous homomorphism of adic rings with a finitely generated ideal of
definition is adic and topologically of finite type if and only if it is taut
and topologically of finite type, equivalently if special-fiber finite-type or
adic completeness conditions hold, equivalently if the target is a closed quotient of a
finite-variable restricted power series algebra or polynomial completion, and
this property is stable under étale completion squares, faithfully flat descent,
and finite products.
-/

@[expose] public section

open TopologicalRing
open TopologicalRing.Ideal

universe u

namespace RingHom

variable {A B : Type u}
variable [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
variable [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]

/-- For a continuous homomorphism between adic rings admitting finitely generated
ideals of definition, adic topological finite type is equivalent to taut
topological finite type, existential and universal special-fiber finite type,
existential and universal adic complete finite type, and closed topological
algebra quotient presentations by finite-variable restricted power series or
polynomial completion. -/
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

namespace TopologicallyOfFiniteType

/-- Adic together with topological finite type is equivalent to taut together
with topological finite type. -/
theorem adic_iff_taut
    {φ : A →+* B} (hφ : Continuous φ) :
    (φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) ↔
      φ.IsTaut ∧ φ.TopologicallyOfFiniteType :=
  (isAdicHom_and_topologicallyOfFiniteType_tfae hφ).out 0 1

/-- Adic together with topological finite type is equivalent to `B` being a
closed quotient of `RestrictedPowerSeries (Fin n) A` as a topological
`A`-algebra. -/
theorem adic_iff_restrictedPowerSeries
    {φ : A →+* B} (hφ : Continuous φ) :
    (φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) ↔
      φ.IsClosedQuotientOfRestrictedPowerSeries :=
  (isAdicHom_and_topologicallyOfFiniteType_tfae hφ).out 0 6

/-- Adic together with topological finite type is equivalent to `B` being a
closed quotient of a polynomial completion `IAdicRestrictedPowerSeries (Fin n) I`. -/
theorem adic_iff_polynomialCompletion
    {φ : A →+* B} (hφ : Continuous φ) :
    (φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) ↔
      φ.IsClosedQuotientOfPolynomialCompletion :=
  (isAdicHom_and_topologicallyOfFiniteType_tfae hφ).out 0 7

/-- Adic together with topological finite type is equivalent to the existence of
an ideal of definition inducing the `I`-adic topology with `B` adically complete
and with finite-type special fiber. -/
theorem adic_iff_completeAlgebra
    {φ : A →+* B} (hφ : Continuous φ) :
    (φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType) ↔
      φ.IsAdicAndTopologicallyFiniteTypeOnSome :=
  (isAdicHom_and_topologicallyOfFiniteType_tfae hφ).out 0 4

end TopologicallyOfFiniteType

end RingHom

namespace TopologicalRing.IsAdicStarRing

/-- Adic topological finite type is stable under étale weak-ideal completion
squares, descends along faithfully flat such squares, and is stable under
finite products of targets among adic rings admitting finitely generated
ideals of definition. -/
theorem isLocalMorphismProperty_isAdicHom_and_topologicallyOfFiniteType :
    IsLocalMorphismProperty
      fun {A B : Type u}
        [CommRing A] [TopologicalSpace A] [IsAdicStarRing A]
        [CommRing B] [TopologicalSpace B] [IsAdicStarRing B]
        (φ : B →+* A) ↦ φ.IsAdicHom ∧ φ.TopologicallyOfFiniteType :=
  sorry

end TopologicalRing.IsAdicStarRing
