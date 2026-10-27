/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import ReasLib.AlgebraicGeometry.Curve.StableOfGenus
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Over
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Stable
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.RingTheory.DiscreteValuationRing.Extension.Basic

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Curve

/-- A smooth projective curve over the fraction field of a discrete valuation ring,
with only constant global functions and genus at least two, acquires a proper stable
family of the same genus after a discrete valuation ring extension inducing a finite
separable extension of fraction fields. -/
theorem existsStableFamilyAfterDVRExtension
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (g : ℕ)
    (h_genus :
      SchemeOverField.genus C (AlgebraicGeometry.topologicalKrullDim_eq_one C)
        h_globalSections = g)
    (hg : 2 ≤ g) :
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
      IsProper f ∧ IsStableFamily f ∧ IsStableFamilyOfGenus g f := sorry

/-- A smooth projective curve over the fraction field of a discrete valuation ring,
with only constant global functions and genus at least two, acquires a proper stable
family of the same genus over the integral closure of the ring in a finite separable
extension of its fraction field. -/
theorem existsStableFamilyOverIntegralClosure
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (g : ℕ)
    (h_genus :
      SchemeOverField.genus C (AlgebraicGeometry.topologicalKrullDim_eq_one C)
        h_globalSections = g)
    (hg : 2 ≤ g) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : Algebra R L)
      (_ : IsScalarTower R K L) (_ : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L)
      (Y : Scheme.{u}) (f : Y ⟶ Spec (CommRingCat.of (integralClosure R L)))
      (genericFiberIso :
        FieldExtension.Over.baseChange K L C ≅ Over.mk
          (pullback.snd f (Spec.map (CommRingCat.ofHom
            (algebraMap (integralClosure R L) L))))),
      IsProper f ∧ IsStableFamily f ∧ IsStableFamilyOfGenus g f := sorry

end AlgebraicGeometry.Curve
