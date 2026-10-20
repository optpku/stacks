module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Integral.Approximation

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicSpace

universe u

#check
  (AlgebraicGeometry.AlgebraicSpace.exists_integralFiniteApproximation :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [AlgebraicSpace.IsIntegralHom f]
      [IsQuasiCompact Y] [IsAbsolutelyQuasiSeparated Y],
      Nonempty (IntegralFiniteApproximation f))
