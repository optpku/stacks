/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.RelativeDimension
public import ReasLib.AlgebraicGeometry.Scheme.Normalization.Stein.Normal
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve
public import ReasLib.AlgebraicGeometry.Scheme.Regular
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein
public import ReasLib.AlgebraicGeometry.Scheme.SpecialFiber

/-!
# Regular models of smooth curves
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The structural morphism of a regular model of a smooth curve over the fraction field of a
discrete valuation ring is Gorenstein. -/
theorem regularModel_gorenstein
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [FiniteType f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    AlgebraicGeometry.Gorenstein f := sorry

/-- The structural morphism of a regular model of a smooth curve over the fraction field of a
discrete valuation ring has relative dimension one. -/
theorem regularModel_relativeDimension
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [FiniteType f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    RelativeDimension f 1 := sorry

/-- Every reduced irreducible component of the special fibre of a regular model of a smooth curve
over the fraction field of a discrete valuation ring is Gorenstein. -/
theorem regularModelSpecialFiberComponent_gorenstein
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [FiniteType f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
    (i : irreducibleComponents (f.fiber (IsLocalRing.closedPoint R))) :
    Scheme.Gorenstein (f.specialFiberComponent i).subscheme := sorry

/-- The special fibre of a regular proper model of a smooth projective curve over the fraction
field of a discrete valuation ring is connected when the curve has only the base field as global
sections. -/
theorem regularModel_connectedSpace_specialFiber
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    ConnectedSpace (f.fiber (IsLocalRing.closedPoint R)) := sorry

/-- The generic fibre of a regular proper model of a smooth projective curve has the expected
geometric integrality, smoothness, and dimension. -/
theorem regularModel_genericFiberProperties
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (globalSectionsMap C.hom))
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R))
    [Flat f] [FiniteType f] [IsProper f] [Scheme.Regular X]
    (genericFiberIso : C ≅ Over.mk
      (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))) :
    Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
      GeometricallyIntegral (pullback.snd f
        (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
      topologicalKrullDim (pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap R K))) : Scheme) = 1 := sorry

end AlgebraicGeometry.Scheme.Hom
