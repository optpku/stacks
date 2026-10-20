/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.Picard
public import stacks_project.Chap55.Lemma_55_9_8_Divisor
public import stacks_project.Chap55.Lemma_55_9_8_Instances
public import stacks_project.Chap55.Situation_55_9_3

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [Field K] [Algebra R K] [IsFractionRing R K]
variable (π : R) (hπ : Irreducible π)
variable (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
variable (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
variable {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
variable [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
variable (genericFiberIso : C ≅ Over.mk
  (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
variable (n : ℕ)
variable (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R)))

/- Lemma 55.9.8 (1): In Situation 55.9.3, the associated sheaf of the normalized
special-fibre divisor has Picard order dividing its multiplicity gcd. -/
@[stacks 0C67] #check
  (AlgebraicGeometry.Scheme.Hom.primitiveSpecialFiberDivisor_picardOrder f n components :
      addOrderOf
        (primitiveSpecialFiberPicardClass f n components) ∣
      specialFiberMultiplicityGcd f n components)

/- Lemma 55.9.8 (2): In Situation 55.9.3, the conormal module of the normalized
special-fibre divisor is invertible and has Picard order dividing its multiplicity gcd. -/
@[stacks 0C67] #check
  (AlgebraicGeometry.Scheme.Hom.primitiveSpecialFiberDivisor_conormalPicardOrder f n components :
    Scheme.Modules.Invertible
        (Scheme.Hom.conormalSheaf
          (primitiveSpecialFiberDivisor f n components).subschemeι) ∧
      addOrderOf
          (primitiveSpecialFiberConormalPicardClass f n components) ∣
        specialFiberMultiplicityGcd f n components)

end AlgebraicGeometry.Scheme.Hom
