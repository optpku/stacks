/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.IntersectionPairing

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.SpecialFiber

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
variable (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
variable (genericFiberIso : C ≅ Over.mk
  (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
variable (n : ℕ)
variable (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))
variable (a b : Fin n → ℤ)

/- Lemma 55.9.6 (1): the component-degree pairing is bilinear over `ℤ` in the
coefficient vector and the Picard class. -/
@[stacks 0C64] #check
  (AlgebraicGeometry.Scheme.Hom.SpecialFiber.degreePairing_isBilinear_of_regularModel
    C h_globalSections f genericFiberIso n components :
    let h_component_proper : ∀ i, IsProper (componentToResidueField f (components i)) :=
      fun i ↦ instIsProperComponentToResidueField f (components i)
    let h_component_dimension : ∀ i, topologicalKrullDim (component f (components i)) ≤ 1 :=
      fun i ↦ component_dimension_le_one C h_globalSections f genericFiberIso n components i
    IsBilinearMap ℤ (degreePairing f n components h_component_proper h_component_dimension))

/- Lemma 55.9.6 (2): pairing with the component divisor class is symmetric in the
coefficient vectors. -/
@[stacks 0C64] #check
  (AlgebraicGeometry.Scheme.Hom.SpecialFiber.degreePairing_swap_of_regularModel
    C h_globalSections f genericFiberIso n components a b :
    let h_component_proper : ∀ i, IsProper (componentToResidueField f (components i)) :=
      fun i ↦ instIsProperComponentToResidueField f (components i)
    let h_component_dimension : ∀ i, topologicalKrullDim (component f (components i)) ≤ 1 :=
      fun i ↦ component_dimension_le_one C h_globalSections f genericFiberIso n components i
    degreePairing f n components h_component_proper h_component_dimension a
        (divisorClass f n components b) =
      degreePairing f n components h_component_proper h_component_dimension b
        (divisorClass f n components a))

end AlgebraicGeometry.Scheme.Hom.SpecialFiber
