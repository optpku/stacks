module

public import ReasLib.AlgebraicGeometry.Scheme.FiniteEtale.UniversalHomeomorphism
public import ReasLib.AlgebraicGeometry.Scheme.FundamentalGroup.Fiber

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- A universal homeomorphism between connected schemes induces a
homeomorphism on their étale fundamental groups at a geometric point. -/
theorem fundamentalGroupIso_of_universalHomeomorphism
    {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversalHomeomorphism f]
    [ConnectedSpace X] [ConnectedSpace Y]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X) :
    IsHomeomorph (AlgebraicGeometry.Scheme.Hom.fundamentalGroupMap f s) := sorry

end AlgebraicGeometry.Scheme
