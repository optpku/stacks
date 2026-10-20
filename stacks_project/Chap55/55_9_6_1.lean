/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.Intersection
public import ReasLib.AlgebraicGeometry.NumericalType.IntersectionForm

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry BigOperators

universe u

/- 55.9.6.1 The intersection form of a regular model is the component-degree pairing for
each of the two associated component divisors. -/
@[stacks 0C65]
#check (AlgebraicGeometry.Scheme.Hom.SpecialFiber.intersectionForm_eq_degreePairings :
  ∀ {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (a b : Fin n → ℤ),
    let h_component_proper :
        ∀ i, IsProper (AlgebraicGeometry.Scheme.Hom.SpecialFiber.componentToResidueField
          f (components i)) :=
      fun i ↦ AlgebraicGeometry.Scheme.Hom.SpecialFiber.instIsProperComponentToResidueField
        f (components i)
    let h_component_dimension :
        ∀ i, topologicalKrullDim
          (AlgebraicGeometry.Scheme.Hom.SpecialFiber.component f (components i)) ≤ 1 :=
      fun i ↦ AlgebraicGeometry.Scheme.Hom.SpecialFiber.component_dimension_le_one
        C h_globalSections f genericFiberIso n components i
    AlgebraicGeometry.Scheme.Hom.SpecialFiber.intersectionForm f n components
        h_component_proper h_component_dimension a b =
      AlgebraicGeometry.Scheme.Hom.SpecialFiber.degreePairing f n components
        h_component_proper h_component_dimension a
        (AlgebraicGeometry.Scheme.Hom.SpecialFiber.divisorClass f n components b) ∧
    AlgebraicGeometry.Scheme.Hom.SpecialFiber.degreePairing f n components
        h_component_proper h_component_dimension a
        (AlgebraicGeometry.Scheme.Hom.SpecialFiber.divisorClass f n components b) =
      AlgebraicGeometry.Scheme.Hom.SpecialFiber.degreePairing f n components
        h_component_proper h_component_dimension b
        (AlgebraicGeometry.Scheme.Hom.SpecialFiber.divisorClass f n components a))
