/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import ReasLib.AlgebraicGeometry.Curve.GenusBounds
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

/- Exercise 111.63.4: for curves, properness is equivalent to projectivity, and
the genus is the degree-one cohomology dimension of the structure sheaf. Thus,
over an algebraically closed field `k`, if `Y` is a smooth proper curve whose
cohomological genus is `10`, then any smooth proper curve `X` admitting a
nonconstant morphism `f : X ⟶ Y` that is not an isomorphism has cohomological
genus at least `10`. -/
@[stacks 0G16] #check
  (AlgebraicGeometry.Curve.genus_ge_10_of_genus_eq_ten_of_nonconstant_not_iso :
    ∀ {k : Type u} [Field k] [IsAlgClosed k]
      (Y : SchemeOverField k) [Curve Y] [IsProper Y.hom] [Smooth Y.hom]
      [GeometricallyIrreducible Y.hom]
      (hY : Scheme.Hom.cohomologyFinrank Y.hom
        (SheafOfModules.unit Y.left.ringCatSheaf : Y.left.Modules) 1 = 10)
      (X : SchemeOverField k) [Curve X] [IsProper X.hom] [Smooth X.hom]
      [GeometricallyIrreducible X.hom] (f : X ⟶ Y) (hf : f.left.IsNonconstant)
      (h_not_iso : ¬ IsIso f), 10 ≤ Scheme.Hom.cohomologyFinrank X.hom
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1)

end AlgebraicGeometry.Curve
