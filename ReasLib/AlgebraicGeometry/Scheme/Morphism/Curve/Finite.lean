/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Birational.FunctionFieldDegree
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Curve

/-!
# Finite morphisms of proper curves

Dominant morphisms between proper curves are finite and induce finite extensions of function
fields.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {k : Type u} [Field k]
variable {X Y : Over (Spec (CommRingCat.of k))}

/-- A dominant morphism between proper curves over a field is finite. -/
instance instIsFiniteOfDominantMorphismOfProperCurves
    [Curve X] [Curve Y] [IsProper X.hom] [IsProper Y.hom]
    (f : X ⟶ Y) [IsDominant f.left] : IsFinite f.left := sorry

/-- A dominant morphism between proper curves induces a finite extension of function fields. -/
theorem finiteFunctionFieldExtension_of_curve
    [Curve X] [Curve Y] [IsProper X.hom] [IsProper Y.hom]
    (f : X ⟶ Y) [IsDominant f.left] :
    f.left.FiniteFunctionFieldExtension := sorry

end AlgebraicGeometry.Scheme.Hom
