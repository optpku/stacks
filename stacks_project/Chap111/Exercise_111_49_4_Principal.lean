/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap111.Definition_111_49_1_Weil
public import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Principal Cartier divisors

On an integral scheme `X`, a unit of the function field determines a Cartier divisor as
the image of its canonical meromorphic representative in `𝒦_X^⁎ / 𝒪_X^⁎`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsIntegral X]

/-- The canonical stalk map `K(X) ⟶ 𝒦_{X, η}` induced by `𝒪_X ⟶ 𝒦_X` at the generic
point. -/
def functionFieldToMeromorphicStalk :
    X.functionField ⟶
      X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.stalk (genericPoint X) :=
  (TopCat.Presheaf.stalkFunctor CommRingCat (genericPoint X)).map
    X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom.hom

/-- The germ map `Γ(X, 𝒦_X) ⟶ 𝒦_{X, η}` on global meromorphic functions. -/
def meromorphicGermGenericPoint :
    X.toLocallyRingedSpace.meromorphicFunctions ⟶
      X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.stalk (genericPoint X) :=
  X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.germ ⊤ (genericPoint X) trivial

/-- The canonical comparison `K(X) ⟶ Γ(X, 𝒦_X)`, sending a rational function to the unique
global meromorphic section whose germ at the generic point is its image in `𝒦_{X, η}`. -/
def functionFieldToMeromorphicFunctions :
    X.functionField ⟶ X.toLocallyRingedSpace.meromorphicFunctions :=
  functionFieldToMeromorphicStalk X ≫
    CommRingCat.ofHom
      { toFun := Function.invFun (meromorphicGermGenericPoint X).hom
        map_one' := sorry
        map_mul' := sorry
        map_zero' := sorry
        map_add' := sorry }

/-- The germ at the generic point of the meromorphic image of a rational function is the
canonical stalk map. -/
theorem functionFieldToMeromorphicFunctions_germ (f : X.functionField) :
    meromorphicGermGenericPoint X (functionFieldToMeromorphicFunctions X f) =
      functionFieldToMeromorphicStalk X f :=
  sorry

/-- The global meromorphic unit associated to a rational function. -/
def meromorphicUnitOfFunctionField (f : X.functionFieldˣ) :
    (X.toLocallyRingedSpace.meromorphicFunctions)ˣ :=
  Units.map (functionFieldToMeromorphicFunctions X).hom.toMonoidHom f

variable [HasSheafify (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X.toTopCat).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]

/-- The principal Cartier divisor associated to a rational function, as the image of its
meromorphic unit in `𝒦_X^⁎ / 𝒪_X^⁎`. -/
def principalCartierDivisor (f : X.functionFieldˣ) : CartierDivisor X :=
  ofMeromorphicUnits X (meromorphicUnitOfFunctionField X f)

/-- A principal Cartier divisor is the cokernel class of the associated meromorphic unit. -/
theorem principalCartierDivisor_eq_ofMeromorphicUnits (f : X.functionFieldˣ) :
    principalCartierDivisor X f =
      ofMeromorphicUnits X (meromorphicUnitOfFunctionField X f) :=
  sorry

/-- The principal Cartier divisor of the unit function is zero. -/
theorem principalCartierDivisor_one : principalCartierDivisor X 1 = 0 :=
  sorry

/-- The principal Cartier divisor of a product is the sum of the principal Cartier
divisors. -/
theorem principalCartierDivisor_mul (f g : X.functionFieldˣ) :
    principalCartierDivisor X (f * g) =
      principalCartierDivisor X f + principalCartierDivisor X g :=
  sorry

/-- The principal Cartier divisor of an inverse is the negation of the principal Cartier
divisor. -/
theorem principalCartierDivisor_inv (f : X.functionFieldˣ) :
    principalCartierDivisor X f⁻¹ = -principalCartierDivisor X f :=
  sorry

/-- The Cartier order of a principal Cartier divisor along a prime divisor is the order of
vanishing of the rational function. -/
theorem cartierOrder_principalCartierDivisor [IsNoetherian X] (f : X.functionFieldˣ)
    (Z : PrimeDivisor X) :
    cartierOrder (principalCartierDivisor X f) Z =
      X.ord (f : X.functionField) Z.genericPoint :=
  sorry

end AlgebraicGeometry.Scheme
