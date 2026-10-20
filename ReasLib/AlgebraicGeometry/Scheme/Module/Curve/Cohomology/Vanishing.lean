/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Cohomology
public import ReasLib.AlgebraicGeometry.Scheme.Module.Curve.Degree
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.IdealSheafData.Lattice
public import ReasLib.AlgebraicGeometry.Scheme.IdealSubobject
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.Pullback

/-!
# Cohomology vanishing for invertible modules on proper curves

This file records degree criteria for the vanishing of first cohomology of invertible modules on
proper curves, including reduced connected curves with possibly reducible underlying schemes.

-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open scoped AlgebraicGeometry
open scoped MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- If an invertible module on a proper curve over an algebraically closed field has degree at
least twice the dimension of the first cohomology of the structure sheaf minus one, then its
first cohomology vanishes. -/
@[stacks 0B90]
theorem firstCohomology_isZero_of_curveDegree_ge
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : Over (Spec (CommRingCat.of k))) [Curve X] [IsProper X.hom]
    {ℒ : X.left.Modules} [Invertible ℒ]
    (hdeg :
      2 * (Scheme.Hom.cohomologyFinrank X.hom
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 : ℤ) - 1 ≤
          curveDegreeOfInvertible X.hom (topologicalKrullDim_eq_one X).le ℒ) :
    IsZero (Scheme.Modules.cohomology ℒ 1) := sorry

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.SchemeOverField

/-- Nonvanishing of the first cohomology of an ideal-twisted invertible module on a reduced,
connected, proper curve produces a reduced connected one-dimensional closed subscheme whose
invertible-module degree is bounded by its Euler characteristic and the intersection degree. -/
theorem exists_connectedSubscheme_degree_le_of_cohomology_one_nonzero
    {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) [IsProper X.hom]
    [IsReduced X.left] [ConnectedSpace X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (L : X.left.Modules) [Scheme.Modules.Invertible L]
    (Z : X.left.IdealSheafData)
    (hZ_dimension : topologicalKrullDim Z.subscheme = 0)
    (hH1 : ¬ IsZero (Scheme.Hom.cohomology X.hom (Z.toModule ⊗ L) 1)) :
    ∃ (Y : X.left.IdealSheafData)
        (hY_dimension : topologicalKrullDim Y.subscheme = 1),
      IsReduced Y.subscheme ∧ ConnectedSpace Y.subscheme ∧
        -- Local instance justification (defeq pin): this supplies the properness-induced
        -- structure-sheaf coherence used by the Euler-characteristic and curve-degree expressions.
        let _ : (SheafOfModules.unit Y.subscheme.ringCatSheaf : Y.subscheme.Modules).IsCoherent :=
          @Scheme.Modules.structureSheaf_isCoherent Y.subscheme
            (LocallyOfFiniteType.isLocallyNoetherian (Y.subschemeι ≫ X.hom))
        Scheme.Modules.curveDegreeOfInvertible (Y.subschemeι ≫ X.hom)
            hY_dimension.le ((Scheme.Modules.pullback Y.subschemeι).obj L) ≤
          -2 * Scheme.Hom.eulerCharacteristic (Y.subschemeι ≫ X.hom)
            (SheafOfModules.unit Y.subscheme.ringCatSheaf : Y.subscheme.Modules) +
            (Module.finrank k
              (Scheme.Hom.globalSectionsAlg ((Z ⊔ Y).subschemeι ≫ X.hom)) : ℤ) := sorry

end AlgebraicGeometry.SchemeOverField
