module

public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Cartier
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Principal
public import ReasLib.AlgebraicGeometry.Scheme.FunctionField.MeromorphicStalk
public import Mathlib.AlgebraicGeometry.Noetherian

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open TopCat.Presheaf
open scoped nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsNoetherian X] [IsIntegral X]

variable [HasSheafify (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X.toTopCat).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]

open Classical in
/-- The order of a Cartier divisor along a prime divisor, via a stalk lift of the germ to a
meromorphic unit and the function-field order of vanishing. -/
def cartierOrder (τ : CartierDivisor X) (Z : PrimeDivisor X) : ℤ :=
  if cartierGerm τ Z.genericPoint = 0 then
    0
  else
    let lift :=
      Function.invFun (cartierCokernelStalk Z.genericPoint).hom
        (cartierGerm τ Z.genericPoint)
    let hU := exists_germ_eq meromorphicUnitsAddPresheaf lift
    let U := Classical.choose hU
    let hm := Classical.choose (Classical.choose_spec hU)
    let s := Classical.choose (Classical.choose_spec (Classical.choose_spec hU))
    let fU :=
      Sheaf.unitsAddSheafValue X.toLocallyRingedSpace.meromorphicFunctionSheaf s
    let hη :=
      ((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
        ⟨Z.genericPoint, ⟨Set.mem_univ _, hm⟩⟩
    let fη :=
      (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.germ U
          (genericPoint X) hη).hom fU
    X.ord ((functionFieldMeromorphicStalkEquiv X).symm fη) Z.genericPoint

/-- A vanishing Cartier germ at the generic point of a prime divisor has order zero. -/
theorem cartierOrder_eq_zero_of_germ_zero (τ : CartierDivisor X) (Z : PrimeDivisor X)
    (h : cartierGerm τ Z.genericPoint = 0) :
    cartierOrder τ Z = 0 := sorry

/-- A local meromorphic-unit representative computes the Cartier order as the function-field
order of vanishing of the germ of that unit at the generic point of `X`. -/
theorem cartierOrder_spec (τ : CartierDivisor X) (Z : PrimeDivisor X)
    {U : X.Opens} (hξ : Z.genericPoint ∈ U)
    (f : ((X.toLocallyRingedSpace.meromorphicFunctionSheaf).presheaf.obj (op U))ˣ)
    (hτ :
      (cartierDivisorAddSheaf X).1.map (homOfLE (le_top : U ≤ ⊤)).op τ =
        ((cokernel.π
              (Sheaf.unitsAddMap
                X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).hom.app
            (op U)).hom
          (Sheaf.unitsAddSheafSection
            X.toLocallyRingedSpace.meromorphicFunctionSheaf f)) :
    cartierOrder τ Z =
      X.ord
        ((functionFieldMeromorphicStalkEquiv X).symm
          ((X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.germ U
              (genericPoint X)
              (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
                ⟨Z.genericPoint, ⟨Set.mem_univ _, hξ⟩⟩)).hom f.val))
        Z.genericPoint := sorry

/-- On an affine local equation `f = a / b` in `𝒦(U)` with `b` a nonzerodivisor, the Cartier
order is the difference of orders of `a` and `b`. -/
theorem cartierOrder_eq_ord_sub (τ : CartierDivisor X) (Z : PrimeDivisor X)
    (U : X.affineOpens) (a b : Γ(X, U))
    (hξ : Z.genericPoint ∈ (U : X.Opens))
    (hb : b ∈ nonZeroDivisors (Γ(X, U)))
    (f : ((X.toLocallyRingedSpace.meromorphicFunctionSheaf).presheaf.obj
      (op (U : X.Opens)))ˣ)
    (hf :
      algebraMap (Γ(X, U))
          ((X.toLocallyRingedSpace.meromorphicFunctionSheaf).presheaf.obj
            (op (U : X.Opens))) a =
        (f : (X.toLocallyRingedSpace.meromorphicFunctionSheaf).presheaf.obj
            (op (U : X.Opens))) *
          algebraMap (Γ(X, U))
            ((X.toLocallyRingedSpace.meromorphicFunctionSheaf).presheaf.obj
              (op (U : X.Opens))) b)
    (hτ :
      (cartierDivisorAddSheaf X).1.map
          (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op τ =
        ((cokernel.π
              (Sheaf.unitsAddMap
                X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).hom.app
            (op (U : X.Opens))).hom
          (Sheaf.unitsAddSheafSection
            X.toLocallyRingedSpace.meromorphicFunctionSheaf f)) :
    cartierOrder τ Z =
      X.ord (algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField
          (X.presheaf.germ (U : X.Opens) Z.genericPoint hξ a)) Z.genericPoint -
      X.ord (algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField
          (X.presheaf.germ (U : X.Opens) Z.genericPoint hξ b)) Z.genericPoint := sorry

/-- An affine meromorphic-unit representative `a / b` computes the Cartier order as the
length of the prime-divisor stalk modulo `a`, minus its length modulo `b`. -/
theorem cartierOrder_eq_length_sub (τ : CartierDivisor X) (Z : PrimeDivisor X)
    (U : X.affineOpens) (a b : Γ(X, U))
    (hξ : Z.genericPoint ∈ (U : X.Opens))
    (hb : b ∈ nonZeroDivisors (Γ(X, U)))
    (f : ((X.toLocallyRingedSpace.meromorphicFunctionSheaf).presheaf.obj
      (op (U : X.Opens)))ˣ)
    (hf :
      algebraMap (Γ(X, U))
          ((X.toLocallyRingedSpace.meromorphicFunctionSheaf).presheaf.obj
            (op (U : X.Opens))) a =
        (f : (X.toLocallyRingedSpace.meromorphicFunctionSheaf).presheaf.obj
            (op (U : X.Opens))) *
          algebraMap (Γ(X, U))
            ((X.toLocallyRingedSpace.meromorphicFunctionSheaf).presheaf.obj
              (op (U : X.Opens))) b)
    (hτ :
      (cartierDivisorAddSheaf X).1.map
          (homOfLE (le_top : (U : X.Opens) ≤ ⊤)).op τ =
        ((cokernel.π
              (Sheaf.unitsAddMap
                X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).hom.app
            (op (U : X.Opens))).hom
          (Sheaf.unitsAddSheafSection
            X.toLocallyRingedSpace.meromorphicFunctionSheaf f)) :
    cartierOrder τ Z =
      ((Ring.ord (X.presheaf.stalk Z.genericPoint)
          (X.presheaf.germ (U : X.Opens) Z.genericPoint hξ a)).toNat : ℤ) -
      ((Ring.ord (X.presheaf.stalk Z.genericPoint)
          (X.presheaf.germ (U : X.Opens) Z.genericPoint hξ b)).toNat : ℤ) := sorry

/-- The nonzero Cartier orders form a locally finite family of prime-divisor supports. -/
theorem locallyFinite_cartierOrder (τ : CartierDivisor X) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      if cartierOrder τ Z = 0 then (∅ : Set X) else (Z.support : Set X) := sorry

/-- The Weil divisor associated to a Cartier divisor on a Noetherian integral scheme. -/
def weilDivisor_ofCartier (τ : CartierDivisor X) : WeilDivisor X :=
  WeilDivisor.ofCoeff X (fun Z ↦ cartierOrder τ Z) (locallyFinite_cartierOrder τ)

/-- The coefficient of the associated Weil divisor of a Cartier divisor is its Cartier
order. -/
theorem weilDivisor_ofCartier_coeff (τ : CartierDivisor X) (Z : PrimeDivisor X) :
    (weilDivisor_ofCartier τ).coeff Z = cartierOrder τ Z :=
  rfl

end AlgebraicGeometry.Scheme
