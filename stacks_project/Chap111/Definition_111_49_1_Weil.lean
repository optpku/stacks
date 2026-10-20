module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.Weil
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Cartier.Weil

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

universe u

/- Effective Cartier divisors on Noetherian integral schemes determine Weil divisors. -/
#check (AlgebraicGeometry.Scheme.weilDivisor_ofEffectiveCartier :
  {X : Scheme.{u}} → [IsNoetherian X] → [IsIntegral X] →
    (D : X.IdealSheafData) → [IsEffectiveCartierDivisor D.subschemeι] → WeilDivisor X)

/- Cartier divisors on Noetherian integral schemes determine Weil divisors. -/
#check (AlgebraicGeometry.Scheme.weilDivisor_ofCartier :
  {X : Scheme.{u}} → [IsNoetherian X] → [IsIntegral X] →
    [HasSheafify (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}] →
    [(Opens.grothendieckTopology X.toTopCat).HasSheafCompose
      (CategoryTheory.forget CommRingCat.{u})] → CartierDivisor X → WeilDivisor X)
