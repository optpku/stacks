/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.Ring.Sheaf.Units.Map
public import ReasLib.AlgebraicGeometry.LocallyRingedSpace.MeromorphicFunction
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.Topology.Sheaves.Stalks

/-!
# Cartier divisors

A Cartier divisor on a scheme `S` is a global section of the quotient sheaf
`𝒦_S^⁎ / 𝒪_S^⁎`, realized as the cokernel of the additive units map along
`𝒪_S ⟶ 𝒦_S`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

variable (S : Scheme.{u})
variable [HasSheafify (Opens.grothendieckTopology S.toTopCat) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology S.toTopCat).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]

/-- The additive sheaf of Cartier divisors is the cokernel of
`𝒪_S^⁎ ⟶ 𝒦_S^⁎`. -/
def cartierDivisorAddSheaf : Sheaf (Opens.grothendieckTopology S.toTopCat) AddCommGrpCat.{u} :=
  cokernel (Sheaf.unitsAddMap S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)

/-- The additive Cartier sheaf is the cokernel of the units map from the structure
sheaf to the meromorphic function sheaf. -/
theorem cartierDivisorAddSheaf_eq_cokernel :
    cartierDivisorAddSheaf S =
      cokernel (Sheaf.unitsAddMap S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom) :=
  rfl

/-- A Cartier divisor on a scheme is a global section of `𝒦_S^⁎ / 𝒪_S^⁎`. -/
abbrev CartierDivisor : Type u :=
  (cartierDivisorAddSheaf S).1.obj (op ⊤)

/-- The type of Cartier divisors is the type of global sections of the additive Cartier sheaf. -/
theorem cartierDivisor_def :
    CartierDivisor S = (cartierDivisorAddSheaf S).1.obj (op ⊤) :=
  rfl

/-- The canonical projection from meromorphic units onto Cartier divisors. -/
def ofMeromorphicUnits
    (f : ((S.toLocallyRingedSpace.meromorphicFunctionSheaf).presheaf.obj (op ⊤))ˣ) :
    CartierDivisor S :=
  ((cokernel.π (Sheaf.unitsAddMap S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).hom.app
      (op ⊤)).hom
    (Sheaf.unitsAddSheafSection S.toLocallyRingedSpace.meromorphicFunctionSheaf f)

/-- `ofMeromorphicUnits` is the global component of the cokernel projection on a meromorphic
unit. -/
theorem ofMeromorphicUnits_eq
    (f : ((S.toLocallyRingedSpace.meromorphicFunctionSheaf).presheaf.obj (op ⊤))ˣ) :
    ofMeromorphicUnits S f =
      ((cokernel.π (Sheaf.unitsAddMap S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).hom.app
          (op ⊤)).hom
        (Sheaf.unitsAddSheafSection S.toLocallyRingedSpace.meromorphicFunctionSheaf f) :=
  rfl

/-- The structure-sheaf units map into meromorphic units composes to zero with the Cartier
projection. -/
theorem unitsAddMap_toMeromorphic_comp_π :
    Sheaf.unitsAddMap S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom ≫
        cokernel.π (Sheaf.unitsAddMap S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom) =
      0 :=
  cokernel.condition _

/-- The short complex `𝒪_S^⁎ ⟶ 𝒦_S^⁎ ⟶ 𝒦_S^⁎ / 𝒪_S^⁎`. -/
def cartierDivisorShortComplex :
    ShortComplex (Sheaf (Opens.grothendieckTopology S.toTopCat) AddCommGrpCat.{u}) :=
  ShortComplex.mk (Sheaf.unitsAddMap S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)
    (cokernel.π (Sheaf.unitsAddMap S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom))
    (unitsAddMap_toMeromorphic_comp_π S)

/-- The defining short complex of the Cartier sheaf is the units map followed by its cokernel
projection. -/
theorem cartierDivisorShortComplex_mk :
    cartierDivisorShortComplex S =
      ShortComplex.mk (Sheaf.unitsAddMap S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)
        (cokernel.π (Sheaf.unitsAddMap S.toLocallyRingedSpace.toMeromorphicFunctionSheafHom))
        (unitsAddMap_toMeromorphic_comp_π S) :=
  rfl

/-- The sequence `0 ⟶ 𝒪_S^⁎ ⟶ 𝒦_S^⁎ ⟶ 𝒦_S^⁎ / 𝒪_S^⁎ ⟶ 0` is short exact. -/
theorem cartierDivisorShortComplex_shortExact :
    (cartierDivisorShortComplex S).ShortExact := sorry

scoped notation "CaDiv(" S ")" => CartierDivisor S

variable {X : Scheme.{u}}

/-- The additive units presheaf of meromorphic functions. -/
def meromorphicUnitsAddPresheaf :
    TopCat.Presheaf AddCommGrpCat.{u} X.toTopCat :=
  (Sheaf.unitsAddSheaf X.toLocallyRingedSpace.meromorphicFunctionSheaf).1

/-- The meromorphic units additive presheaf is the underlying presheaf of the units sheaf. -/
theorem meromorphicUnitsAddPresheaf_eq :
    meromorphicUnitsAddPresheaf =
      (Sheaf.unitsAddSheaf X.toLocallyRingedSpace.meromorphicFunctionSheaf).1 :=
  rfl

variable [HasSheafify (Opens.grothendieckTopology X.toTopCat) AddCommGrpCat.{u}]
variable [(Opens.grothendieckTopology X.toTopCat).HasSheafCompose
  (CategoryTheory.forget CommRingCat.{u})]

/-- The additive presheaf underlying the Cartier divisor sheaf. -/
def cartierDivisorAddPresheaf :
    TopCat.Presheaf AddCommGrpCat.{u} X.toTopCat :=
  (cartierDivisorAddSheaf X).1

/-- The Cartier additive presheaf is the underlying presheaf of the Cartier sheaf. -/
theorem cartierDivisorAddPresheaf_eq :
    cartierDivisorAddPresheaf = (cartierDivisorAddSheaf X).1 :=
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

/-- The Cartier cokernel on stalks is the stalk map of the sheaf cokernel projection. -/
theorem cartierCokernelStalk_eq (x : X) :
    cartierCokernelStalk x =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (cokernel.π
          (Sheaf.unitsAddMap X.toLocallyRingedSpace.toMeromorphicFunctionSheafHom)).hom :=
  rfl

/-- The projection from meromorphic-unit germs to Cartier germs is surjective. -/
theorem cartierCokernelStalk_surjective (x : X) :
    Function.Surjective (cartierCokernelStalk x).hom := sorry

end AlgebraicGeometry.Scheme
