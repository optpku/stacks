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
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Intersection.CurveDegree
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import stacks_project.Chap53.Definition_53_8_1_Genus
public import stacks_project.Chap55.Situation_55_9_3
public import stacks_project.Chap55.Lemma_55_9_1_SpecialFiber
public import stacks_project.Chap55.Lemma_55_9_6_Components
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber.GenusFormula

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry BigOperators

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Lemma 55.11.2 -/
@[stacks 0CA3] #check
  (AlgebraicGeometry.Scheme.Hom.SpecialFiber.genus_eq_specialFiber_formula :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Field K] [Algebra R K] [IsFractionRing R K]
      (π : R) (hπ : Irreducible π)
      (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom] [IsProper C.hom]
      (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
      [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
      (genericFiberIso : C ≅ Over.mk
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
      (n : ℕ)
      (components : Fin n ≃ irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))),
      let h_component_proper :
          ∀ i, IsProper (SpecialFiber.componentToResidueField f (components i)) :=
        fun i => inferInstance
      let h_component_dimension :
          ∀ i, topologicalKrullDim (SpecialFiber.component f (components i)) ≤ 1 :=
        fun i => SpecialFiber.component_dimension_le_one
          C h_globalSections f genericFiberIso n components i
      (SchemeOverField.genus C
        (AlgebraicGeometry.topologicalKrullDim_eq_one C) h_globalSections : ℚ) =
        1 + ∑ i, (f.specialFiberMultiplicities (components i) : ℚ) *
          ((@Module.finrank
              ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))
              (Scheme.Hom.globalSectionsAlg
                (SpecialFiber.componentToResidueField f (components i)))
              inferInstance inferInstance
              (@Algebra.toModule
                ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R))
                (Scheme.Hom.globalSectionsAlg
                  (SpecialFiber.componentToResidueField f (components i)))
                inferInstance inferInstance
                (Scheme.Hom.globalSectionsAlgebra
                  (SpecialFiber.componentToResidueField f (components i)))) : ℚ) *
            ((Scheme.Hom.cohomologyFinrank
              (SpecialFiber.component f (components i)).toSpecΓ
              (SheafOfModules.unit
                (SpecialFiber.component f (components i)).ringCatSheaf :
                (SpecialFiber.component f (components i)).Modules) 1 : ℚ) - 1) -
          (SpecialFiber.componentDegree f (components i) (h_component_proper i)
            (h_component_dimension i)
            ((Scheme.Modules.pullback (SpecialFiber.componentInclusion f (components i))).obj
              (f.specialFiberComponent (components i)).associatedSheaf) : ℚ) / 2))

end AlgebraicGeometry.Scheme.Hom
