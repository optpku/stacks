module

public import stacks_project.Chap111.Definition_111_49_1_Cartier
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.EffectiveCartier.IdealSheaf
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.MeromorphicSection
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.OrderOfVanishing
public import ReasLib.AlgebraicGeometry.Scheme.Divisor.Prime.PointClosure
public import ReasLib.AlgebraicGeometry.Scheme.Module.Invertible.MeromorphicSection.OfGlobal
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.OrderOfVanishing
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Associated Weil divisors of Cartier data

On a Noetherian integral scheme, an effective Cartier divisor and a Cartier
divisor determine Weil divisors by the length-order recipe along prime divisors.
-/

@[expose] public section

open Classical
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open TopCat.Presheaf
open scoped nonZeroDivisors

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsNoetherian X] [IsIntegral X]

/-- The sheaf associated to an effective Cartier divisor is invertible. -/
instance instInvertible_associatedSheaf (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] :
    Modules.Invertible (IdealSheafData.associatedSheaf D) :=
  sorry

/-- The canonical section of an effective Cartier divisor remains nonzero as a meromorphic
section. -/
theorem canonicalSection_toMeromorphicSection_ne_zero (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] :
    Modules.toMeromorphicSection (IdealSheafData.associatedSheaf D)
      (IdealSheafData.canonicalSection D) ≠ 0 :=
  sorry

/-- The Weil divisor associated to an effective Cartier divisor on a Noetherian integral
scheme. -/
def weilDivisor_ofEffectiveCartier (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] : WeilDivisor X :=
  let s := Modules.toMeromorphicSection (IdealSheafData.associatedSheaf D)
    (IdealSheafData.canonicalSection D)
  if h : s = 0 then 0
  else nonzeroMeromorphicSectionWeilDivisor X (IdealSheafData.associatedSheaf D) s h

/-- If the canonical meromorphic section is nonzero, the associated Weil divisor is the
meromorphic-section Weil divisor. -/
theorem weilDivisor_ofEffectiveCartier_eq_of_ne_zero (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι]
    (h : Modules.toMeromorphicSection (IdealSheafData.associatedSheaf D)
      (IdealSheafData.canonicalSection D) ≠ 0) :
    weilDivisor_ofEffectiveCartier D =
      nonzeroMeromorphicSectionWeilDivisor X (IdealSheafData.associatedSheaf D)
        (Modules.toMeromorphicSection (IdealSheafData.associatedSheaf D)
          (IdealSheafData.canonicalSection D)) h :=
  sorry

/-- The associated Weil coefficient vanishes when the generic point of the prime divisor does
not lie on the effective Cartier divisor. -/
theorem weilDivisor_ofEffectiveCartier_coeff_eq_zero_of_not_mem (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] (Z : PrimeDivisor X)
    (hZ : Z.genericPoint ∉ D.support) :
    (weilDivisor_ofEffectiveCartier D).coeff Z = 0 :=
  sorry

/-- On a local nonzerodivisor equation, the associated Weil coefficient is the order of
vanishing of that equation in the function field. -/
theorem effectiveCartierOrder_spec (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] (Z : PrimeDivisor X)
    (U : X.affineOpens) (f : Γ(X, U))
    (hξ : Z.genericPoint ∈ (U : X.Opens))
    (hf : f ∈ nonZeroDivisors (Γ(X, U)))
    (hgen : D.ideal U = Ideal.span ({f} : Set (Γ(X, U)))) :
    (weilDivisor_ofEffectiveCartier D).coeff Z =
      X.ord (algebraMap (X.presheaf.stalk Z.genericPoint) X.functionField
        (X.presheaf.germ (U : X.Opens) Z.genericPoint hξ f)) Z.genericPoint :=
  sorry

/-- On a local nonzerodivisor equation, the associated Weil coefficient is the length of the
quotient of the local ring of `Z` by that equation. -/
theorem effectiveCartierOrder_eq_length (D : X.IdealSheafData)
    [IsEffectiveCartierDivisor D.subschemeι] (Z : PrimeDivisor X)
    (U : X.affineOpens) (f : Γ(X, U))
    (hξ : Z.genericPoint ∈ (U : X.Opens))
    (hf : f ∈ nonZeroDivisors (Γ(X, U)))
    (hgen : D.ideal U = Ideal.span ({f} : Set (Γ(X, U)))) :
    (weilDivisor_ofEffectiveCartier D).coeff Z =
      ((Ring.ord (X.presheaf.stalk Z.genericPoint)
          (X.presheaf.germ (U : X.Opens) Z.genericPoint hξ f)).toNat : ℤ) :=
  sorry

variable [HasSheafify (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X.toTopCat).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]

/-- The additive presheaf underlying the Cartier divisor sheaf. -/
def cartierDivisorAddPresheaf :
    TopCat.Presheaf AddCommGrpCat.{u} X.toTopCat :=
  (cartierDivisorAddSheaf X).1

/-- Unfold the Cartier additive presheaf as the underlying presheaf of the Cartier sheaf. -/
theorem cartierDivisorAddPresheaf_eq :
    cartierDivisorAddPresheaf = (cartierDivisorAddSheaf X).1 :=
  rfl

/-- The additive units presheaf of meromorphic functions. -/
def meromorphicUnitsAddPresheaf :
    TopCat.Presheaf AddCommGrpCat.{u} X.toTopCat :=
  (Sheaf.unitsAddSheaf X.toLocallyRingedSpace.meromorphicFunctionSheaf).1

/-- Unfold the meromorphic units additive presheaf. -/
theorem meromorphicUnitsAddPresheaf_eq :
    meromorphicUnitsAddPresheaf =
      (Sheaf.unitsAddSheaf X.toLocallyRingedSpace.meromorphicFunctionSheaf).1 :=
  rfl

/-- The germ of a Cartier divisor at a point. -/
def cartierGerm (τ : CartierDivisor X) (x : X) :=
  (TopCat.Presheaf.Γgerm
    (cartierDivisorAddPresheaf : TopCat.Presheaf AddCommGrpCat.{u} X.toTopCat) x).hom τ

/-- The germ of a Cartier divisor is the image of the global section under `Γgerm`. -/
theorem cartierGerm_eq (τ : CartierDivisor X) (x : X) :
    cartierGerm τ x =
      (TopCat.Presheaf.Γgerm
        (cartierDivisorAddPresheaf : TopCat.Presheaf AddCommGrpCat.{u} X.toTopCat) x).hom τ :=
  rfl

/-- The stalk map induced by the cokernel projection `𝒦^⁎ ⟶ 𝒦^⁎ / 𝒪^⁎`. -/
def cartierCokernelStalk (x : X) :
    TopCat.Presheaf.stalk
        (meromorphicUnitsAddPresheaf : TopCat.Presheaf AddCommGrpCat.{u} X.toTopCat) x ⟶
      TopCat.Presheaf.stalk
        (cartierDivisorAddPresheaf : TopCat.Presheaf AddCommGrpCat.{u} X.toTopCat) x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    (cokernel.π (Sheaf.unitsAddMap X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).hom

/-- Unfold the Cartier cokernel on stalks. -/
theorem cartierCokernelStalk_eq (x : X) :
    cartierCokernelStalk x =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (cokernel.π
          (Sheaf.unitsAddMap X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).hom :=
  rfl

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
    X.ord
      (Function.invFun
        (algebraMap X.functionField
          (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.stalk (genericPoint X)))
        fη)
      Z.genericPoint

/-- A vanishing Cartier germ at the generic point of a prime divisor has order zero. -/
theorem cartierOrder_eq_zero_of_germ_zero (τ : CartierDivisor X) (Z : PrimeDivisor X)
    (h : cartierGerm τ Z.genericPoint = 0) :
    cartierOrder τ Z = 0 :=
  sorry

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
        (Function.invFun
          (algebraMap X.functionField
            (X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.stalk
              (genericPoint X)))
          ((X.toLocallyRingedSpace.meromorphicFunctionSheaf.presheaf.germ U
              (genericPoint X)
              (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
                ⟨Z.genericPoint, ⟨Set.mem_univ _, hξ⟩⟩)).hom f.val))
        Z.genericPoint :=
  sorry

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
          (X.presheaf.germ (U : X.Opens) Z.genericPoint hξ b)) Z.genericPoint :=
  sorry

/-- The nonzero Cartier orders form a locally finite family of prime-divisor supports. -/
theorem locallyFinite_cartierOrder (τ : CartierDivisor X) :
    LocallyFinite fun Z : PrimeDivisor X ↦
      if cartierOrder τ Z = 0 then (∅ : Set X) else (Z.support : Set X) :=
  sorry

/-- The Weil divisor associated to a Cartier divisor on a Noetherian integral scheme. -/
def weilDivisor_ofCartier (τ : CartierDivisor X) : WeilDivisor X :=
  WeilDivisor.ofCoeff X (fun Z ↦ cartierOrder τ Z) (locallyFinite_cartierOrder τ)

/-- The coefficient of the associated Weil divisor of a Cartier divisor is its Cartier
order. -/
theorem weilDivisor_ofCartier_coeff (τ : CartierDivisor X) (Z : PrimeDivisor X) :
    (weilDivisor_ofCartier τ).coeff Z = cartierOrder τ Z :=
  rfl

end AlgebraicGeometry.Scheme
