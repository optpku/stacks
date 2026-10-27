/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Model.FiniteType
public import ReasLib.AlgebraicGeometry.Curve.StableOfGenus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Stable

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom.Model

/-- Two proper stable models of the same genus of a smooth proper curve over
the fraction field of a discrete valuation ring, with only constant global
functions, admit a unique isomorphism preserving their generic-fibre markings. -/
theorem existsUnique_stableIso
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [IsProper C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (g : ℕ)
    (h_genus :
      SchemeOverField.genus C (topologicalKrullDim_eq_one C) h_globalSections = g)
    (X X' : Model R K C) [IsProper X.base] [IsProper X'.base]
    [IsStableFamily X.base] [IsStableFamily X'.base]
    (hX : IsStableFamilyOfGenus g X.base)
    (hX' : IsStableFamilyOfGenus g X'.base) :
    ∃! e : Over.mk X.base ≅ Over.mk X'.base, Model.IsMorphism X X' e.hom := sorry

end AlgebraicGeometry.Scheme.Hom.Model
