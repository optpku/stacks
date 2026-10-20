/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Module.Picard.Model.Torsion

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AddSubgroup
open scoped AlgebraicGeometry

universe u

/- Lemma 55.13.4: In Situation 55.9.3, restriction from `X.PicardGroup[h]` to the
Picard group of the reduced special fibre is injective when `h` is invertible in
the residue field. -/
@[stacks 0CAE] #check
  (AlgebraicGeometry.Scheme.Hom.picardPullback_specialFiberReduction_injective :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [Scheme.Hom.FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (h : ℤ)
    (h_unit : IsUnit (h : IsLocalRing.ResidueField R)),
    Set.InjOn
      (Scheme.Hom.picardPullback
        (Scheme.reductionι (f.fiber (IsLocalRing.closedPoint R)) ≫
          f.fiberι (IsLocalRing.closedPoint R)))
      X.PicardGroup[h])
