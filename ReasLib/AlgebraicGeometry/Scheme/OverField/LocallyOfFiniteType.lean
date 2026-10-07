module

public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.OverField

/-!
# Locally finite type morphisms of schemes over a field

This module records a locally-finite-type property of the underlying morphism of schemes over a
field.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.SchemeOverField

variable {k : Type u} [Field k]

/-- The underlying morphism of a morphism from a locally algebraic scheme over a field is locally
of finite type. -/
instance instLocallyOfFiniteTypeLeftOfLocallyAlgebraic
    {X Y : SchemeOverField k} (f : Y ⟶ X) [LocallyAlgebraic Y] :
    LocallyOfFiniteType f.left := sorry

end AlgebraicGeometry.SchemeOverField
