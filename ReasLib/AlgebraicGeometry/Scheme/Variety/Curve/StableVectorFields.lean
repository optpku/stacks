/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalTail
public import ReasLib.AlgebraicGeometry.Scheme.OverField.RationalBridge
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve.VectorFields

@[expose] public section

open AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.RingedSpace.Hom
open AlgebraicGeometry.SchemeOverField
open SheafOfModules

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

/-- Every relative structure-sheaf derivation on a proper connected at-worst-nodal curve
of genus at least two without rational tails or bridges vanishes. -/
theorem derivation_eq_zero_of_stable
    {k : Type u} [Field k] [IsAlgClosed k]
    (X : SchemeOverField k) [IsProper X.hom] [ConnectedSpace X.left]
    (h_dimension : topologicalKrullDim X.left = 1)
    (h_nodal : atWorstNodal X)
    (h_genus : 2 ≤ Scheme.Hom.cohomologyFinrank X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1)
    (h_no_tail : ¬ Nonempty (RationalTail X))
    (h_no_bridge : ¬ Nonempty (AlgebraicGeometry.RationalBridge X))
    (D : derivations X.hom.toShHom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules)) :
    derivationIsZero X D := sorry

end AlgebraicGeometry.Curve
