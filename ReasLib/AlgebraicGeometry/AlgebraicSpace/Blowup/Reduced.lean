module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.RelativeProj
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Reduced

/-!
# Reducedness of blowups of algebraic spaces
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Blowup

/-- The blowup of a reduced algebraic space in a quasi-coherent ideal sheaf is reduced. -/
@[stacks 085W]
theorem isReduced {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : IdealSubobject X} [IsQuasiCoherent I] (π : Blowup X I) [IsReduced X] :
    IsReduced π.space := sorry

end AlgebraicGeometry.AlgebraicSpace.Blowup
