module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Proper
public import ReasLib.AlgebraicGeometry.Scheme.Variety.Properties

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

variable {k : Type u} [Field k]

/-- Every morphism between projective varieties over a field is proper. -/
instance instIsProperHomOfProjectiveVarieties
    {X Y : SchemeOverField k} [ProjectiveVariety X] [ProjectiveVariety Y]
    (f : X ⟶ Y) : IsProper f.left := sorry

end AlgebraicGeometry
