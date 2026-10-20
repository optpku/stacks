/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import ReasLib.AlgebraicGeometry.Scheme.ClosedSubscheme.IrreducibleComponent
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Nonconstant
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- A morphism from a proper scheme of dimension at most one over a field to a separated scheme
is finite if its restriction to every one-dimensional irreducible component is nonconstant. -/
theorem isFinite_of_dimLEOne_of_nonconstant_irreducibleComponents
    {k : Type u} [Field k] {X Y : SchemeOverField k}
    [IsSeparated Y.hom] [IsProper X.hom] (f : X ⟶ Y)
    (hdim : topologicalKrullDim X.left ≤ 1)
    (hcomponent : ∀ Z : irreducibleComponents X.left,
      topologicalKrullDim (X.left.irreducibleComponentSubscheme Z) = 1 →
        (X.left.irreducibleComponentSubschemeι Z ≫ f.left).IsNonconstant) :
    IsFinite f.left := sorry

end AlgebraicGeometry.Scheme.Hom
