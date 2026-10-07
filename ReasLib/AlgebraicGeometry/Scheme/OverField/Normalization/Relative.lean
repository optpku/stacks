module

public import ReasLib.AlgebraicGeometry.Scheme.OverField.LocallyOfFiniteType
public import ReasLib.AlgebraicGeometry.Scheme.OverField.Normalization.FiniteType

/-!
# Relative normalization of schemes over a field

This module records finiteness of relative normalization for locally algebraic schemes over a
field.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField.RelativeNormalization

variable {k : Type u} [Field k]

/-- For a quasi-compact morphism of locally algebraic schemes over a field with reduced source,
the relative normalization morphism is finite. -/
instance instIsFiniteFromNormalization
    {X Y : SchemeOverField k} (f : Y ⟶ X)
    [QuasiCompact f.left] [LocallyAlgebraic X] [LocallyAlgebraic Y] [IsReduced Y.left] :
    IsFinite f.left.fromNormalization := sorry

end AlgebraicGeometry.SchemeOverField.RelativeNormalization
