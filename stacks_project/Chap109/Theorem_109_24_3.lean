/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Curve.StableReduction

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

/- Theorem 109.24.3 (1) -/
@[stacks 0E98] #check (AlgebraicGeometry.Curve.existsStableFamilyAfterDVRExtension :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (g : ℕ)
    (h_genus :
      SchemeOverField.genus C (AlgebraicGeometry.topologicalKrullDim_eq_one C)
        h_globalSections = g)
    (hg : 2 ≤ g),
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsDomain R') (_ : IsDiscreteValuationRing R')
      (_ : Algebra R R') (_ : IsExtensionOfDiscreteValuationRings R R')
      (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra R K')
      (_ : Algebra R' K') (_ : IsScalarTower R K K') (_ : IsScalarTower R R' K')
      (_ : IsFractionRing R' K') (_ : FiniteDimensional K K')
      (_ : Algebra.IsSeparable K K')
      (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of R'))
      (genericFiberIso :
        FieldExtension.Over.baseChange K K' C ≅ Over.mk
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R' K'))))),
      IsProper f ∧ IsStableFamily f ∧ IsStableFamilyOfGenus g f)

/- Theorem 109.24.3 (2) -/
@[stacks 0E98] #check (AlgebraicGeometry.Curve.existsStableFamilyOverIntegralClosure :
    ∀ (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (g : ℕ)
    (h_genus :
      SchemeOverField.genus C (AlgebraicGeometry.topologicalKrullDim_eq_one C)
        h_globalSections = g)
    (hg : 2 ≤ g),
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Algebra R L)
      (_ : IsScalarTower R K L) (_ : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L)
      (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of (integralClosure R L)))
      (genericFiberIso :
        FieldExtension.Over.baseChange K L C ≅ Over.mk
          (pullback.snd f (Spec.map (CommRingCat.ofHom
            (algebraMap (integralClosure R L) L))))),
      IsProper f ∧ IsStableFamily f ∧ IsStableFamilyOfGenus g f)
