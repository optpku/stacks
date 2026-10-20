/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Model.Regular.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.MinimalModel
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.ProjectiveSpace.Over

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.RegularModel

/-- For a smooth projective genus-zero curve with constant global functions, the existence
of two non-isomorphic minimal models forces the special fibre of every minimal model to be
the projective line over the residue field. -/
@[stacks 0CDA]
theorem specialFiber_iso_projectiveLine_of_nonunique
    (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field K] [Algebra R K] [IsFractionRing R K]
    (C : SchemeOverField K) [Curve C] [Smooth C.hom] [Projective C.hom]
    (h_globalSections : Function.Bijective (Scheme.Hom.globalSectionsMap C.hom))
    (h_genus : SchemeOverField.genus C (topologicalKrullDim_eq_one C) h_globalSections = 0)
    (h_nonunique : ∃ M N : RegularModel R K C,
      IsMinimalModel M.base ∧ IsMinimalModel N.base ∧ ¬ Isomorphic M N)
    (M : RegularModel R K C) [IsMinimalModel M.base] :
    Nonempty
      (Over.mk (M.base.fiberOverSpecResidueField (IsLocalRing.closedPoint R)).hom ≅
        ProjectiveSpace.schemeOver
          ((Spec (CommRingCat.of R)).residueField (IsLocalRing.closedPoint R)) 1) := sorry

end AlgebraicGeometry.Scheme.Hom.RegularModel
