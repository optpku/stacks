/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Model.Regular.Existence
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A smooth projective curve of positive genus over the fraction field of a discrete
valuation ring, whose global functions are precisely the constants, has a minimal regular
model unique up to an isomorphism preserving the chosen generic-fibre identification. -/
theorem exists_minimalModel_uniqueUpToIso
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (h_genus : 0 < SchemeOverField.genus C (topologicalKrullDim_eq_one C) h_globalSections) :
    ∃ M : RegularModel R K C, IsMinimalModel M.base ∧
      ∀ N : RegularModel R K C, IsMinimalModel N.base →
        RegularModel.Isomorphic M N := sorry

end AlgebraicGeometry.Scheme.Hom
