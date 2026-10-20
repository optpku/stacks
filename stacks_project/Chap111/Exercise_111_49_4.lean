module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Cartier.Principal
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

universe u

/- Exercise 111.49.4: The principal Cartier divisor of a nonzero rational function has the
same associated Weil divisor as the rational function. -/
@[stacks 02F7] #check (AlgebraicGeometry.Scheme.weilDivisor_ofCartier_principalCartierDivisor :
  {X : Scheme.{u}} → [IsNoetherian X] → [IsIntegral X] →
    [HasSheafify (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}] →
    [(Opens.grothendieckTopology X.toTopCat).HasSheafCompose
      (CategoryTheory.forget CommRingCat.{u})] →
    (f : X.functionFieldˣ) →
    weilDivisor_ofCartier (principalCartierDivisor X f) = principalWeilDivisor X f)
