/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.CotangentComplex.NaiveComparison.Self
public import ReasLib.RingTheory.CotangentComplex.HomologyZero
public import ReasLib.RingTheory.Extension.Cotangent.ExtOne
public import ReasLib.CategoryTheory.DerivedCategory.Ext
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Equiv

/-!
# Low-degree extensions of the cotangent complex

The canonical comparison with the naive cotangent complex induces an additive
equivalence on first extension groups. Zeroth extensions are maps out of the
module of Kähler differentials.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory DerivedCategory HomologicalComplex ComplexShape
open CategoryTheory.Limits
open Algebra Algebra.Generators Algebra.Extension
open Algebra.CotangentComplex
open CommRingCat.Under.CotangentComplex
open scoped DerivedExt

namespace RingHom.SquareZeroExtension

variable (B : Type u) [CommRing B]

/-- The coefficient object `N[0]` in `D(Mod B)`. -/
abbrev coeffSingle (N : Type u) [AddCommGroup N] [Module B N] :
    DerivedCategory (ModuleCat.{u} B) :=
  (singleFunctor (ModuleCat.{u} B) (0 : ℤ)).obj (ModuleCat.of B N)

/-- Unfolding of `coeffSingle` as the degree-zero single object on `N`. -/
theorem coeffSingle_eq (N : Type u) [AddCommGroup N] [Module B N] :
    coeffSingle B N =
      (singleFunctor (ModuleCat.{u} B) (0 : ℤ)).obj (ModuleCat.of B N) :=
  rfl


variable (A B N : Type u) [CommRing A] [CommRing B] [Algebra A B]
variable [AddCommGroup N] [Module B N]

/-- The derived Ext¹ class of a Hom representative on `NL_{B/A}`. -/
private def toNaiveExt (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    Ext⁽(1 : ℤ)⁾(DerivedCategory.Q.obj
        (selfNaiveComplex (CommRingCat.of A) (Under.mk (CommRingCat.ofHom (algebraMap A B)))), coeffSingle B N) :=
  DerivedCategory.Q.map
      (extendMap (extOneHomUnderChain A B f) embeddingDownNat) ≫
    DerivedCategory.Q.map
      (extendSingleIso embeddingDownNat (ModuleCat.of B N) 1 (-1 : ℤ) rfl).hom ≫
    ((DerivedCategory.singleFunctors (ModuleCat B)).shiftIso (1 : ℤ) (-1) 0
        (add_neg_cancel (1 : ℤ))).inv.app (ModuleCat.of B N)

-- The public representative formulas unfold this private construction.
set_option backward.privateInPublic true in
/-- The Ext¹ class of `L_{B/A}` attached to a Hom representative, by precomposition
with the canonical full-to-naive comparison. -/
private def toDerivedExt
    (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N) :=
  ShiftedHom.comp (ShiftedHom.mk₀ (0 : ℤ) rfl (derivedToNaiveObject A B))
    (toNaiveExt A B N f) (add_zero (1 : ℤ))

-- Public computations and specifications use the private representative construction in this file.
set_option backward.privateInPublic true in
/-- The full-cotangent class of a conormal map depends only on its naive Ext class. -/
theorem extOneNaiveDerivedHom_well_defined :
    ∀ f g, (LinearMap.range (LinearMap.lcomp B N
        (Generators.self A B).toExtension.cotangentComplex)).quotientRel f g →
      toDerivedExt A B N f = toDerivedExt A B N g := sorry

-- Public computations and specifications use the private representative construction in this file.
set_option backward.privateInPublic true in
/-- The zero conormal map represents the zero full-cotangent Ext class. -/
theorem extOneNaiveDerivedHom_map_zero :
    toDerivedExt A B N 0 = 0 := sorry

-- Public computations and specifications use the private representative construction in this file.
set_option backward.privateInPublic true in
/-- The full-cotangent quotient comparison preserves addition of naive Ext classes. -/
theorem extOneNaiveDerivedHom_map_add (ξ η : extOneNaiveCotangent A B N) :
    Quotient.liftOn (ξ + η) (fun f ↦ toDerivedExt A B N f)
      (extOneNaiveDerivedHom_well_defined A B N) =
      (Quotient.liftOn ξ (fun f ↦ toDerivedExt A B N f)
      (extOneNaiveDerivedHom_well_defined A B N)) + (Quotient.liftOn η (fun f ↦ toDerivedExt A B N f)
      (extOneNaiveDerivedHom_well_defined A B N)) := sorry

-- Public computations and specifications use the private representative construction in this file.
set_option backward.privateInPublic true in
/-- The canonical additive comparison from naive Ext¹ to full-cotangent Ext¹. -/
def extOneNaiveDerivedHom :
    extOneNaiveCotangent A B N →+ Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N) where
  toFun ξ := Quotient.liftOn ξ (fun f ↦ toDerivedExt A B N f)
      (extOneNaiveDerivedHom_well_defined A B N)
  map_zero' := extOneNaiveDerivedHom_map_zero A B N
  map_add' := extOneNaiveDerivedHom_map_add A B N

/-- Truncation in degrees at least minus one induces a bijection on first extension classes
with coefficients concentrated in degree zero. -/
theorem extOneNaiveDerivedHom_bijective :
    Function.Bijective (extOneNaiveDerivedHom A B N) := sorry

/-- The canonical naive-to-derived Ext¹ comparison as an additive equivalence,
with its inverse determined by an explicit certificate of bijectivity. -/
def extOneNaiveDerivedEquivOf
    (hbij : Function.Bijective (extOneNaiveDerivedHom A B N)) :
    extOneNaiveCotangent A B N ≃+ Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N) :=
  AddEquiv.ofBijective (extOneNaiveDerivedHom A B N) hbij

-- Public computations and specifications use the private representative construction in this file.
set_option backward.privateInPublic true in
/-- With explicit bijectivity, the first-extension comparison sends a conormal
representative to its canonical derived class. -/
theorem extOneNaiveDerivedEquivOf_mk
    (hbij : Function.Bijective (extOneNaiveDerivedHom A B N))
    (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    extOneNaiveDerivedEquivOf A B N hbij (extOneNaiveCotangent_mk A B N f) =
      toDerivedExt A B N f := rfl

/-- The canonical additive equivalence from naive Ext¹ to full-cotangent Ext¹,
using `extOneNaiveDerivedHom_bijective` as its inverse certificate. The explicit
form `extOneNaiveDerivedEquivOf` accepts this certificate from the caller. -/
def extOneNaiveDerivedEquiv :
    extOneNaiveCotangent A B N ≃+ Ext⁽(1 : ℤ)⁾(derived A B, coeffSingle B N) :=
  extOneNaiveDerivedEquivOf A B N
    (extOneNaiveDerivedHom_bijective A B N)

-- Public computations and specifications use the private representative construction in this file.
set_option backward.privateInPublic true in
/-- The first-extension comparison sends a conormal representative to its canonical derived class. -/
theorem extOneNaiveDerivedEquiv_mk
    (f : (Generators.self A B).toExtension.Cotangent →ₗ[B] N) :
    extOneNaiveDerivedEquiv A B N (extOneNaiveCotangent_mk A B N f) =
      toDerivedExt A B N f := rfl

-- The public representative formulas unfold this private construction.
set_option backward.privateInPublic true in
/-- The unshifted morphism `L_{B/A} ⟶ N[0]` attached to a B-linear map out of `Ω[B⁄A]`. -/
private def homKaehlerDerived (α : Ω[B⁄A] →ₗ[B] N) :
    derived A B ⟶ coeffSingle B N :=
  DerivedCategory.Q.map (augmentation A B) ≫
    (singleFunctorIsoCompQ (ModuleCat.{u} B) (0 : ℤ)).inv.app (ModuleCat.of B Ω[B⁄A]) ≫
      (singleFunctor (ModuleCat.{u} B) (0 : ℤ)).map (ModuleCat.ofHom α)

-- The public representative formulas unfold this private construction.
set_option backward.privateInPublic true in
/-- The Hom representative of an Ext⁰ class, obtained from `H^0` of `homKaehlerDerived`
transported along `homologyZeroIso`. -/
private def homOfExtZero
    (e : Ext⁽(0 : ℤ)⁾(derived A B, coeffSingle B N)) :
    Ω[B⁄A] →ₗ[B] N :=
  ((homologyZeroIso A B).inv ≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) (0 : ℤ)).inv.app
      (Algebra.cotangentComplex A B) ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B) (0 : ℤ)).map
      ((ShiftedHom.homEquiv (0 : ℤ) rfl).symm e) ≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} B) (0 : ℤ)).hom.app
      ((CochainComplex.singleFunctor (ModuleCat.{u} B) (0 : ℤ)).obj (ModuleCat.of B N)) ≫
    (singleObjHomologySelfIso (ComplexShape.up ℤ) (0 : ℤ) (ModuleCat.of B N)).hom).hom

-- Public computations and specifications use the private representative construction in this file.
set_option backward.privateInPublic true in
/-- Recovering the map on differentials from its derived augmentation class is the identity. -/
theorem extZeroHomEquiv_left_inv (α : Ω[B⁄A] →ₗ[B] N) :
    homOfExtZero A B N
      (ShiftedHom.homEquiv (0 : ℤ) rfl (homKaehlerDerived A B N α)) = α := sorry

-- Public computations and specifications use the private representative construction in this file.
set_option backward.privateInPublic true in
/-- The augmentation class of the map on zeroth homology recovers the original Ext⁰ class. -/
theorem extZeroHomEquiv_right_inv
    (e : Ext⁽(0 : ℤ)⁾(derived A B, coeffSingle B N)) :
    ShiftedHom.homEquiv (0 : ℤ) rfl
      (homKaehlerDerived A B N (homOfExtZero A B N e)) = e := sorry

-- Public computations and specifications use the private representative construction in this file.
set_option backward.privateInPublic true in
/-- The Ext⁰ identification `Hom_B(Ω[B⁄A], N) ≃ Ext⁽0⁾(L_{B/A}, N)`. -/
def extZeroHomEquiv :
    (Ω[B⁄A] →ₗ[B] N) ≃ Ext⁽(0 : ℤ)⁾(derived A B, coeffSingle B N) where
  toFun α := ShiftedHom.homEquiv (0 : ℤ) rfl (homKaehlerDerived A B N α)
  invFun e := homOfExtZero A B N e
  left_inv := extZeroHomEquiv_left_inv A B N
  right_inv := extZeroHomEquiv_right_inv A B N

-- Public computations and specifications use the private representative construction in this file.
set_option backward.privateInPublic true in
/-- The forward map of `extZeroHomEquiv` is `ShiftedHom.homEquiv` of `homKaehlerDerived`. -/
theorem extZeroHomEquiv_apply (α : Ω[B⁄A] →ₗ[B] N) :
    extZeroHomEquiv A B N α =
      ShiftedHom.homEquiv (0 : ℤ) rfl (homKaehlerDerived A B N α) :=
  rfl


end SquareZeroExtension

end RingHom
