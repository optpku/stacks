/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.Intersection

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.SpecialFiber

/-- The component-degree pairing of a regular proper model of a smooth projective curve
is bilinear over `ℤ` on coefficient vectors and Picard classes. -/
theorem degreePairing_isBilinear_of_regularModel
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    let h_component_proper : ∀ i, IsProper (componentToResidueField f (components i)) :=
      fun i ↦ instIsProperComponentToResidueField f (components i)
    let h_component_dimension : ∀ i, topologicalKrullDim (component f (components i)) ≤ 1 :=
      fun i ↦ component_dimension_le_one C h_globalSections f genericFiberIso n components i
    IsBilinearMap ℤ (degreePairing f n components h_component_proper
      h_component_dimension) := sorry

/-- For a regular proper model of a smooth projective curve, pairing a coefficient vector
with the component divisor class of another vector is symmetric in the two vectors. -/
theorem degreePairing_swap_of_regularModel
    {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (n : ℕ)
    (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
    (a b : Fin n → ℤ) :
    let h_component_proper : ∀ i, IsProper (componentToResidueField f (components i)) :=
      fun i ↦ instIsProperComponentToResidueField f (components i)
    let h_component_dimension : ∀ i, topologicalKrullDim (component f (components i)) ≤ 1 :=
      fun i ↦ component_dimension_le_one C h_globalSections f genericFiberIso n components i
    degreePairing f n components h_component_proper h_component_dimension a
        (divisorClass f n components b) =
      degreePairing f n components h_component_proper h_component_dimension b
        (divisorClass f n components a) := sorry

end AlgebraicGeometry.Scheme.Hom.SpecialFiber
