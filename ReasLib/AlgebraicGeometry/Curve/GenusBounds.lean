/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Nonconstant
public import ReasLib.AlgebraicGeometry.Scheme.Module.Cohomology.GlobalSections
public import ReasLib.AlgebraicGeometry.Scheme.OverField
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Curve

/-- A nonconstant morphism between smooth proper geometrically irreducible curves has source
cohomological genus at least target cohomological genus. -/
theorem genus_le_genus_of_nonconstant
    {k : Type u} [Field k] [IsAlgClosed k]
    (Y : SchemeOverField k) [Curve Y] [IsProper Y.hom] [Smooth Y.hom]
    [GeometricallyIrreducible Y.hom]
    (X : SchemeOverField k) [Curve X] [IsProper X.hom] [Smooth X.hom]
    [GeometricallyIrreducible X.hom]
    (f : X ⟶ Y) (hf : f.left.IsNonconstant) :
    Scheme.Hom.cohomologyFinrank Y.hom
        (SheafOfModules.unit Y.left.ringCatSheaf : Y.left.Modules) 1 ≤
      Scheme.Hom.cohomologyFinrank X.hom
        (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 := sorry

/-- A nonconstant non-isomorphic morphism from a smooth proper curve to a smooth proper curve with
cohomological genus ten has source cohomological genus at least ten. -/
theorem genus_ge_10_of_genus_eq_ten_of_nonconstant_not_iso
    {k : Type u} [Field k] [IsAlgClosed k]
    (Y : SchemeOverField k) [Curve Y] [IsProper Y.hom] [Smooth Y.hom]
    [GeometricallyIrreducible Y.hom]
    (hY : Scheme.Hom.cohomologyFinrank Y.hom
      (SheafOfModules.unit Y.left.ringCatSheaf : Y.left.Modules) 1 = 10)
    (X : SchemeOverField k) [Curve X] [IsProper X.hom] [Smooth X.hom]
    [GeometricallyIrreducible X.hom]
    (f : X ⟶ Y) (hf : f.left.IsNonconstant) (h_not_iso : ¬ IsIso f) :
    10 ≤ Scheme.Hom.cohomologyFinrank X.hom
      (SheafOfModules.unit X.left.ringCatSheaf : X.left.Modules) 1 := sorry

end AlgebraicGeometry.Curve
