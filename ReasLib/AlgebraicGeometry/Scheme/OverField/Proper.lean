module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.SchemeOverField

/-- A morphism from a projective scheme over a field to a separated scheme over that
field is proper. -/
instance hom_isProper {k : Type u} [Field k]
    {X Y : SchemeOverField k} [IsSeparated X.hom] [Projective Y.hom]
    (f : Y ⟶ X) : IsProper f.left := sorry

end AlgebraicGeometry.SchemeOverField
