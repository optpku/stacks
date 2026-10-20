/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.LocalRing.Pullback

/-!
# Dual-number algebra maps associated to derivations

A derivation defines an algebra map into dual numbers, whose pullback against
the constant inclusion is the diagonal of the derivation's kernel.
-/

public section

open TrivSqZeroExt
open scoped DualNumber

universe u v

namespace Derivation

variable {Λ : Type u} {R : Type v} [CommRing Λ] [CommRing R] [Algebra Λ R]

/-- The sum of the constant inclusion and the infinitesimal derivation sends one to one. -/
private theorem dualNumber_map_one (D : Derivation Λ R R) :
    ((inlAlgHom Λ R R).toLinearMap +
      ((inrHom R R).restrictScalars Λ).comp D.toLinearMap) 1 = 1 := sorry

/-- The sum of the constant inclusion and the infinitesimal derivation preserves products. -/
private theorem dualNumber_map_mul (D : Derivation Λ R R) (left right : R) :
    ((inlAlgHom Λ R R).toLinearMap +
        ((inrHom R R).restrictScalars Λ).comp D.toLinearMap) (left * right) =
      ((inlAlgHom Λ R R).toLinearMap +
          ((inrHom R R).restrictScalars Λ).comp D.toLinearMap) left *
        ((inlAlgHom Λ R R).toLinearMap +
          ((inrHom R R).restrictScalars Λ).comp D.toLinearMap) right := sorry

/-- The algebra map sending `a` to the dual number with scalar part `a` and
infinitesimal part `D a`. -/
def toDualNumberAlgHom (D : Derivation Λ R R) : R →ₐ[Λ] DualNumber R :=
  AlgHom.ofLinearMap
    ((inlAlgHom Λ R R).toLinearMap +
      ((inrHom R R).restrictScalars Λ).comp D.toLinearMap)
    (dualNumber_map_one D) (dualNumber_map_mul D)

/-- The dual-number algebra map evaluates to `inl a + inr (D a)`. -/
theorem toDualNumberAlgHom_apply (D : Derivation Λ R R) (value : R) :
    D.toDualNumberAlgHom value = inl value + inr (D value) := sorry

/-- The pullback against the constant inclusion consists of equal pairs on which
the derivation vanishes. -/
theorem mem_dualNumberPullback_iff (D : Derivation Λ R R) {left right : R} :
    (left, right) ∈ AlgHom.pullback D.toDualNumberAlgHom (inlAlgHom Λ R R) ↔
      left = right ∧ D left = 0 := sorry

variable {k : Type v} [Field k] [Algebra Λ k]

/-- The dual-number algebra map of a derivation on a field is a local homomorphism. -/
instance toDualNumberAlgHom_isLocalHom (D : Derivation Λ k k) :
    IsLocalHom D.toDualNumberAlgHom := sorry

end Derivation

namespace DualNumber

variable {Λ : Type u} {R : Type v} [CommRing Λ] [CommRing R] [Algebra Λ R]

/-- The dual-number endomorphism associated to a derivation sends `a + vε` to
`a + (v + D a)ε`. -/
def autOfDerivation (D : Derivation Λ R R) : DualNumber R →ₐ[Λ] DualNumber R :=
  lift ⟨(D.toDualNumberAlgHom, ε), eps_mul_eps, fun _ ↦ commute_eps_left _⟩

/-- The derivation-induced dual-number endomorphism adds the derivation of the scalar
coefficient to the infinitesimal coefficient. -/
theorem autOfDerivation_apply (D : Derivation Λ R R) (value : DualNumber R) :
    autOfDerivation D value = inl value.fst + inr (value.snd + D value.fst) := sorry

end DualNumber
