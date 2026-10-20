module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Blowup.RelativeProj
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Divisor.EffectiveCartier.Pullback

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Blowup

/-- The pullback of every effective Cartier divisor along a blowup morphism of
algebraic spaces is defined. -/
theorem pullbackDefined {S : Scheme.{u}} {X : AlgebraicSpace S}
    {I : IdealSubobject X} [IsQuasiCoherent I] (π : Blowup X I)
    (D : ClosedSubspace X) [IsEffectiveCartierDivisor D.ι] :
    D.IsPullbackDefined π.hom :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Blowup
