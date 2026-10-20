/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Model.Numerical

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Lemma 55.13.2 (1): In Situation 55.9.3, normalized component degrees descend uniquely to
the Picard group of the associated numerical type. -/
@[stacks 0CAC] #check
  (AlgebraicGeometry.Scheme.Hom.existsUniquePicardToNumerical :
    ∀ {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Field K] [Algebra R K] [IsFractionRing R K]
      (π : R) (hπ : Irreducible π)
      (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
      (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
      [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
      (genericFiberIso : C ≅ Over.mk
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
      (T : NumericalType)
      (components : Fin T.n ≃ irreducibleComponents
        (f.fiber (IsLocalRing.closedPoint R)))
      (hT : T.IsAssociatedTo C h_globalSections f genericFiberIso components),
      ∃! φ : C.left.PicardGroup →+ T.PicardGroup,
        ∀ x : X.PicardGroup,
          φ (AlgebraicGeometry.Scheme.Hom.genericFiberPicardRestriction
            f genericFiberIso x) =
            T.toPicardGroup
              (AlgebraicGeometry.Scheme.Hom.SpecialFiber.normalizedDegreeMap
                C h_globalSections f genericFiberIso T.n components x))

/- Lemma 55.13.2 (2): The kernel consists of restrictions of model classes of zero degree on
every indexed special-fibre component. -/
@[stacks 0CAC] #check
  (AlgebraicGeometry.Scheme.Hom.picardToNumerical_ker_iff :
    ∀ {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
      [Field K] [Algebra R K] [IsFractionRing R K]
      (π : R) (hπ : Irreducible π)
      (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
      (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
      {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
      [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
      (genericFiberIso : C ≅ Over.mk
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
      (T : NumericalType)
      (components : Fin T.n ≃ irreducibleComponents
        (f.fiber (IsLocalRing.closedPoint R)))
      (hT : T.IsAssociatedTo C h_globalSections f genericFiberIso components)
      (y : C.left.PicardGroup),
      y ∈ (AlgebraicGeometry.Scheme.Hom.picardToNumerical
        π hπ C h_globalSections f genericFiberIso T components hT).ker ↔
        ∃ x : X.PicardGroup,
          AlgebraicGeometry.Scheme.Hom.genericFiberPicardRestriction
            f genericFiberIso x = y ∧
          ∀ i : Fin T.n,
            AlgebraicGeometry.Scheme.Hom.SpecialFiber.componentDegree
              f (components i)
              (AlgebraicGeometry.Scheme.Hom.SpecialFiber.instIsProperComponentToResidueField
                f (components i))
              (AlgebraicGeometry.Scheme.Hom.SpecialFiber.component_dimension_le_one
                C h_globalSections f genericFiberIso T.n components i)
              ((Scheme.Modules.pullback
                (AlgebraicGeometry.Scheme.Hom.SpecialFiber.componentInclusion
                  f (components i))).obj (Scheme.PicardGroup.repr x)) = 0 )
