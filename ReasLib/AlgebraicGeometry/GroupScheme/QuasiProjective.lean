module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import ReasLib.AlgebraicGeometry.Scheme.Algebraic
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.QuasiProjective
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

universe u

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.GroupScheme

/-- The structure morphism of an algebraic group scheme over a field is quasi-projective. -/
instance instQuasiProjective {k : Type u} [Field k]
    (G : SchemeOverField k) [GrpObj G] [Algebraic G] : QuasiProjective G.hom := sorry

end AlgebraicGeometry.GroupScheme
