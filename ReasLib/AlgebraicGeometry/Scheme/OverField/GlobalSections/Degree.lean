/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.GlobalSections.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.DimensionFunction
public import ReasLib.AlgebraicGeometry.Scheme.OverField.ClosedPoints
public import ReasLib.AlgebraicGeometry.Scheme.UniversallyCatenary.FiniteType

/-!
# Degrees of global-sections fields

This module relates the degree of the global-sections field of a proper, reduced, connected
scheme over a field to curve degrees, closed-point residue degrees, and degrees of
zero-dimensional closed subschemes.
-/

@[expose] public section

open CategoryTheory TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField.GlobalSections

variable {k : Type u} [Field k]

/-- The degree over the base field of the global-sections algebra of a scheme over that field. -/
noncomputable abbrev finrank (X : SchemeOverField k) : ℕ :=
  Module.finrank k (Scheme.Hom.globalSectionsAlg X.hom)

/-- The degree of the global-sections field divides the degree of every finite locally free
module of constant rank on a proper, reduced, connected scheme of dimension at most one. -/
theorem finrank_dvd_curveDegree (X : SchemeOverField k) [IsProper X.hom]
    [IsReduced X.left] [ConnectedSpace X.left]
    (hdim : topologicalKrullDim X.left ≤ 1) (ℰ : X.left.Modules) (n : ℕ)
    [Scheme.Modules.IsFiniteLocallyFreeOfRank n ℰ] :
    (finrank X : ℤ) ∣ Scheme.Modules.curveDegree X.hom hdim ℰ n := sorry

/-- The degree of the global-sections field divides the residue-field degree at every closed
point of a proper, reduced, connected scheme over a field. -/
theorem finrank_dvd_residueFieldDegree (X : SchemeOverField k) [IsProper X.hom]
    [IsReduced X.left] [ConnectedSpace X.left] (x : closedPoints X.left) :
    finrank X ∣ Module.finrank k (X.left.residueField x.1) := sorry

/-- The degree of the global-sections field divides the global-sections degree of every
zero-dimensional closed subscheme of a proper, reduced, connected scheme over a field. -/
theorem finrank_dvd_zeroDimensionalClosedSubschemeDegree
    (X : SchemeOverField k) [IsProper X.hom] [IsReduced X.left] [ConnectedSpace X.left]
    (D : X.left.IdealSheafData) (hDdim : topologicalKrullDim D.subscheme = 0) :
    finrank X ∣
      Module.finrank k (Scheme.Hom.globalSectionsAlg (D.subschemeι ≫ X.hom)) := sorry

end AlgebraicGeometry.SchemeOverField.GlobalSections

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- At a relative zero-dimensional point of a proper scheme over `k`, the residue degree is the
`k`-dimension of the global-sections algebra of its reduced point closure. -/
theorem residueDegree_eq_pointClosureFinrank (X : SchemeOverField k) [IsProper X.hom]
    (x : X.left)
    (hx : X.hom.relativeDimensionFunction
      (fun _ : Spec (CommRingCat.of k) ↦ 0) x = 0) :
    X.hom.residueDegree x =
      Module.finrank k
        (Scheme.Hom.globalSectionsAlg (Scheme.PointClosure.ι x ≫ X.hom)) := sorry

end AlgebraicGeometry.SchemeOverField
