module

public import stacks_project.Chap111.Exercise_111_49_4_Principal
public import stacks_project.Chap111.Definition_111_49_1_Weil
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Principal
import Mathlib.Tactic.CrossRefAttribute

/-!
# Cartier divisors of rational functions

On an integral scheme, a rational function determines a Cartier divisor as the class of
its meromorphic image, and the associated Weil divisor agrees with the Weil divisor of
the function.
-/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

/-- Exercise 111.49.4: On an integral scheme `X`, the Cartier divisor assigned to a rational
function `f : X.functionFieldˣ` is `principalCartierDivisor X f`, the image of `f` in
`𝒦_X^⁎ / 𝒪_X^⁎`. The Weil divisor associated to this Cartier divisor agrees with the Weil
divisor associated to `f`. -/
@[stacks 02F7]
theorem weilDivisor_ofCartier_principalCartierDivisor
    {X : Scheme.{u}} [IsNoetherian X] [IsIntegral X]
    [HasSheafify (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X.toTopCat).HasSheafCompose
      (CategoryTheory.forget CommRingCat.{u})]
    (f : X.functionFieldˣ) :
    weilDivisor_ofCartier (principalCartierDivisor X f) = principalWeilDivisor X f :=
  sorry

end AlgebraicGeometry.Scheme
