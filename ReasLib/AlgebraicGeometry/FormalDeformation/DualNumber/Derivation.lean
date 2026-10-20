/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.RingTheory.Derivation.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber

/-!
# Derivations and dual-number morphisms

Derivations of the residue field over the base ring correspond to morphisms from the
residue-field object to the dual-number object.
-/

@[expose] public section

open CategoryTheory TrivSqZeroExt

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

namespace ArtinianLocalAlgCat

/-- A derivation defines a local, residue-compatible morphism to the dual numbers by
`a ↦ inl a + inr (D a)`. -/
def derivationToDualNumber (D : Derivation Λ k k) : residue Λ k ⟶ dualNumber Λ k :=
  let coefficientMap : k → DualNumber k := fun scalar ↦ inl scalar + inr (D scalar)
  let laws :
      (coefficientMap 1 = 1) ∧
      (∀ scalar other, coefficientMap (scalar * other) =
        coefficientMap scalar * coefficientMap other) ∧
      (coefficientMap 0 = 0) ∧
      (∀ scalar other, coefficientMap (scalar + other) =
        coefficientMap scalar + coefficientMap other) ∧
      (∀ base, coefficientMap (algebraMap Λ k base) = algebraMap Λ (DualNumber k) base) ∧
      (∀ hom : algebraHom (residue Λ k) (dualNumber Λ k),
        (∀ scalar, hom scalar = coefficientMap scalar) →
          IsLocalHom hom ∧ ∀ h_local : IsLocalHom hom,
            residueCompat hom h_local = residueIsoHom (residue Λ k)) := sorry
  let hom : k →ₐ[Λ] DualNumber k :=
    { toFun := coefficientMap
      map_one' := laws.1
      map_mul' := laws.2.1
      map_zero' := laws.2.2.1
      map_add' := laws.2.2.2.1
      commutes' := laws.2.2.2.2.1 }
  let compatibility := laws.2.2.2.2.2 hom (fun _ ↦ rfl)
  Hom.of hom compatibility.1 (compatibility.2 compatibility.1)

/-- The morphism associated to a derivation has scalar coefficient `a` and infinitesimal
coefficient `D a`. -/
theorem derivationToDualNumber_apply (D : Derivation Λ k k) (a : k) :
    (derivationToDualNumber D).hom a = inl a + inr (D a) := sorry

/-- The infinitesimal coefficient of a residue-compatible dual-number morphism is a
derivation over the base ring. -/
def derivationOfHom (f : residue Λ k ⟶ dualNumber Λ k) : Derivation Λ k k :=
  let coefficientMap : k → k := fun scalar ↦ snd (f.hom scalar)
  let laws :
      (∀ scalar other, coefficientMap (scalar + other) =
        coefficientMap scalar + coefficientMap other) ∧
      (∀ (base : Λ) (scalar : k),
        coefficientMap (base • scalar) = base • coefficientMap scalar) ∧
      (coefficientMap 1 = 0) ∧
      (∀ scalar other, coefficientMap (scalar * other) =
        scalar • coefficientMap other + other • coefficientMap scalar) := sorry
  { toFun := coefficientMap
    map_add' := laws.1
    map_smul' := laws.2.1
    map_one_eq_zero' := laws.2.2.1
    leibniz' := laws.2.2.2 }

/-- The derivation associated to a dual-number morphism extracts its infinitesimal
coefficient. -/
theorem derivationOfHom_apply (f : residue Λ k ⟶ dualNumber Λ k) (a : k) :
    derivationOfHom f a = snd (f.hom a) := sorry

/-- Derivations of the residue field over the base ring correspond to residue-compatible
local morphisms from the residue-field object to the dual numbers. -/
def derivationHomEquiv (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
    [Module.Finite Λ k] : Derivation Λ k k ≃ (residue Λ k ⟶ dualNumber Λ k) :=
  let inverseLaws :
      Function.LeftInverse (derivationOfHom (Λ := Λ) (k := k)) derivationToDualNumber ∧
      Function.RightInverse (derivationOfHom (Λ := Λ) (k := k)) derivationToDualNumber := sorry
  { toFun := derivationToDualNumber
    invFun := derivationOfHom
    left_inv := inverseLaws.1
    right_inv := inverseLaws.2 }

/-- The derivation equivalence sends a derivation to its associated dual-number morphism. -/
theorem derivationHomEquiv_apply (D : Derivation Λ k k) :
    derivationHomEquiv Λ k D = derivationToDualNumber D := sorry

/-- The inverse derivation equivalence extracts the derivation of a dual-number morphism. -/
theorem derivationHomEquiv_symm_apply (f : residue Λ k ⟶ dualNumber Λ k) :
    (derivationHomEquiv Λ k).symm f = derivationOfHom f := sorry

end ArtinianLocalAlgCat
