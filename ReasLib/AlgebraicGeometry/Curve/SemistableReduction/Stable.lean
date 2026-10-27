/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Curve.SemistableReduction.Characterization
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Stable
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A smooth projective curve over the fraction field of a discrete valuation ring,
with only constant global functions and genus at least two, has semistable reduction
if and only if it is the generic fibre of a proper stable family over that ring. -/
theorem hasSemistableReduction_iff_existsStableFamily
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (h_genus : 2 ≤ SchemeOverField.genus C
      (AlgebraicGeometry.topologicalKrullDim_eq_one C) h_globalSections) :
    hasSemistableReduction R K C ↔
      ∃ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
        (genericFiberIso : C ≅ Over.mk
          (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap R K))))),
        IsProper f ∧ IsStableFamily f := sorry

end AlgebraicGeometry.Scheme.Hom
