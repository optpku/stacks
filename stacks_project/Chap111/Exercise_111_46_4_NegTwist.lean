module

public import ReasLib.AlgebraicGeometry.Scheme.Module.NegTwist

open AlgebraicGeometry CategoryTheory

universe u

#check (AlgebraicGeometry.Scheme.Modules.negTwist :
  ∀ {X : Scheme.{u}} (L : X.Modules) (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι], X.Modules)

#check (AlgebraicGeometry.Scheme.Modules.vanishesOnDivisor_iff_memNegTwist :
  ∀ {X : Scheme.{u}} {L : X.Modules} [Scheme.Modules.Invertible L]
    (s : L.sections) (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι],
    Scheme.Modules.vanishesOnDivisor s D ↔ Scheme.Modules.memNegTwist s D)
