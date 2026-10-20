module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.AssociatedCartier

@[expose] public section

universe u

/- Exercise 111.49.3: On any scheme, the local nonzerodivisor equations of an effective
Cartier divisor glue to its associated Cartier divisor. -/
#check (AlgebraicGeometry.Scheme.cartierDivisor_ofEffectiveCartier :
    ∀ {S : AlgebraicGeometry.Scheme.{u}},
      [CategoryTheory.HasSheafify (Opens.grothendieckTopology S.toTopCat) AddCommGrpCat.{u}] →
      [(Opens.grothendieckTopology S.toTopCat).HasSheafCompose
        (CategoryTheory.forget CommRingCat.{u})] →
      (D : S.IdealSheafData) →
      [AlgebraicGeometry.IsEffectiveCartierDivisor D.subschemeι] →
      AlgebraicGeometry.Scheme.CartierDivisor S)
