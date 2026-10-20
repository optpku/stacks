/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.ProperDualizingComplex.Curve
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Nodal
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalTail
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalBridge
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.ArithmeticGenus

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme
open Scheme.DerivedQCoh.ProperDualizingComplex
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- A proper at-worst-nodal curve with constant global functions, genus at least two, and no
rational tails or bridges has an ample canonical dualizing module. -/
theorem curveDualizingModule_isAmple_of_stable
    {k : Type u} [Field k] (X : SchemeOverField k) [IsProper X.hom]
    (h_dimension : topologicalKrullDim X.left = 1)
    (hΓ : Function.Bijective (Scheme.Hom.globalSectionsMap X.hom))
    (h_nodal : atWorstNodal X)
    (h_no_tail : ¬ Nonempty (RationalTail X))
    (h_no_bridge : ¬ Nonempty (AlgebraicGeometry.RationalBridge X))
    (h_genus : (2 : ℕ) ≤ genus X h_dimension hΓ) :
    Scheme.Modules.isAmpleObject (curveDualizingModule X.hom) := sorry

end AlgebraicGeometry.SchemeOverField
