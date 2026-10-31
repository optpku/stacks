/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.RingTheory.Derivation.Basic
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber
public import ReasLib.RingTheory.DualNumber.Derivation

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

/-- The dual-number algebra map associated to a derivation preserves the canonical
residue-field identifications. -/
theorem derivation_residue_compat (D : Derivation Λ k k) :
    residueCompat (A := residue Λ k) (B := dualNumber Λ k)
        D.toDualNumberAlgHom (Derivation.toDualNumberAlgHom_isLocalHom D) =
      residueIsoHom (residue Λ k) := sorry

/-- A derivation defines its local residue-compatible dual-number morphism using
its canonical dual-number algebra homomorphism. -/
def derivationToDualNumber (D : Derivation Λ k k) : residue Λ k ⟶ dualNumber Λ k :=
  Hom.of D.toDualNumberAlgHom (Derivation.toDualNumberAlgHom_isLocalHom D)
    (derivation_residue_compat D)

/-- The canonical morphism has the supplied dual-number algebra homomorphism. -/
theorem derivationToDualNumber_hom (D : Derivation Λ k k) :
    (derivationToDualNumber D).hom = D.toDualNumberAlgHom := rfl

/-- The morphism associated to a derivation has scalar coefficient `a` and infinitesimal
coefficient `D a`. -/
theorem derivationToDualNumber_apply (D : Derivation Λ k k) (a : k) :
    (derivationToDualNumber D).hom a = inl a + inr (D a) :=
  D.toDualNumberAlgHom_apply a

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
    derivationOfHom f a = snd (f.hom a) := rfl

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
    derivationHomEquiv Λ k D = derivationToDualNumber D := rfl

/-- The inverse derivation equivalence extracts the derivation of a dual-number morphism. -/
theorem derivationHomEquiv_symm_apply (f : residue Λ k ⟶ dualNumber Λ k) :
    (derivationHomEquiv Λ k).symm f = derivationOfHom f := rfl

end ArtinianLocalAlgCat
