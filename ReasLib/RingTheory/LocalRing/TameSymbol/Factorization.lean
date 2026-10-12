/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Ring.NonZeroDivisors
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.LocalRing.ResidueField.Map

@[expose] public section

/-!
# Tame-symbol values from chosen local factorizations

This module records the explicit local data used in the norm-product formula for a tame symbol.
Choice independence is deliberately not part of this owner.
-/

noncomputable section

open IsLocalRing
open scoped BigOperators nonZeroDivisors

universe u v

namespace TameSymbol

/-- Chosen factorization data for two nonzerodivisors in a finite extension of a
one-dimensional Noetherian local ring. -/
structure Factorization
    (A : Type u) (B : Type v) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    [CommRing B] [Algebra A B] [Module.Finite A B] (a₁ a₂ : A) where
  dimension_eq_one : ringKrullDim A = 1
  a₁_nonZeroDivisor : a₁ ∈ nonZeroDivisors A
  a₂_nonZeroDivisor : a₂ ∈ nonZeroDivisors A
  extension_injective : Function.Injective (algebraMap A B)
  annihilatedByMaximalIdealPower : ∃ n : ℕ,
    maximalIdeal A ^ n • (⊤ : Submodule A B) ≤ (Algebra.linearMap A B).range
  maximals : Finset (MaximalSpectrum B)
  maximals_complete : ∀ j : MaximalSpectrum B, j ∈ maximals
  liesOver : ∀ j : MaximalSpectrum B, j.asIdeal.LiesOver (maximalIdeal A)
  π : (j : MaximalSpectrum B) → Localization.AtPrime j.asIdeal
  π_nonZeroDivisor : ∀ j, π j ∈ nonZeroDivisors (Localization.AtPrime j.asIdeal)
  u₁ : (j : MaximalSpectrum B) → (Localization.AtPrime j.asIdeal)ˣ
  u₂ : (j : MaximalSpectrum B) → (Localization.AtPrime j.asIdeal)ˣ
  e₁ : MaximalSpectrum B → ℕ
  e₂ : MaximalSpectrum B → ℕ
  m : MaximalSpectrum B → ℕ
  factorization₁ : ∀ j,
    algebraMap B (Localization.AtPrime j.asIdeal) (algebraMap A B a₁) =
      (u₁ j : Localization.AtPrime j.asIdeal) * π j ^ e₁ j
  factorization₂ : ∀ j,
    algebraMap B (Localization.AtPrime j.asIdeal) (algebraMap A B a₂) =
      (u₂ j : Localization.AtPrime j.asIdeal) * π j ^ e₂ j
  m_spec : ∀ j, m j =
    (Module.length (Localization.AtPrime j.asIdeal)
      (Localization.AtPrime j.asIdeal ⧸ Ideal.span {π j})).toNat

namespace Factorization

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable [CommRing B] [Algebra A B] [Module.Finite A B]
variable {a₁ a₂ : A}

/-- Build chosen factorization data from its extension conditions, local coordinates, and
factorization and length identities. -/
def ofLocalData
    (dimension_eq_one : ringKrullDim A = 1)
    (a₁_nonZeroDivisor : a₁ ∈ nonZeroDivisors A)
    (a₂_nonZeroDivisor : a₂ ∈ nonZeroDivisors A)
    (extension_injective : Function.Injective (algebraMap A B))
    (annihilatedByMaximalIdealPower : ∃ n : ℕ,
      maximalIdeal A ^ n • (⊤ : Submodule A B) ≤ (Algebra.linearMap A B).range)
    (maximals : Finset (MaximalSpectrum B))
    (maximals_complete : ∀ j : MaximalSpectrum B, j ∈ maximals)
    (liesOver : ∀ j : MaximalSpectrum B, j.asIdeal.LiesOver (maximalIdeal A))
    (π : (j : MaximalSpectrum B) → Localization.AtPrime j.asIdeal)
    (π_nonZeroDivisor : ∀ j, π j ∈ nonZeroDivisors (Localization.AtPrime j.asIdeal))
    (u₁ u₂ : (j : MaximalSpectrum B) → (Localization.AtPrime j.asIdeal)ˣ)
    (e₁ e₂ m : MaximalSpectrum B → ℕ)
    (factorization₁ : ∀ j,
      algebraMap B (Localization.AtPrime j.asIdeal) (algebraMap A B a₁) =
        (u₁ j : Localization.AtPrime j.asIdeal) * π j ^ e₁ j)
    (factorization₂ : ∀ j,
      algebraMap B (Localization.AtPrime j.asIdeal) (algebraMap A B a₂) =
        (u₂ j : Localization.AtPrime j.asIdeal) * π j ^ e₂ j)
    (m_spec : ∀ j, m j =
      (Module.length (Localization.AtPrime j.asIdeal)
        (Localization.AtPrime j.asIdeal ⧸ Ideal.span {π j})).toNat) :
    Factorization A B a₁ a₂ where
  dimension_eq_one := dimension_eq_one
  a₁_nonZeroDivisor := a₁_nonZeroDivisor
  a₂_nonZeroDivisor := a₂_nonZeroDivisor
  extension_injective := extension_injective
  annihilatedByMaximalIdealPower := annihilatedByMaximalIdealPower
  maximals := maximals
  maximals_complete := maximals_complete
  liesOver := liesOver
  π := π
  π_nonZeroDivisor := π_nonZeroDivisor
  u₁ := u₁
  u₂ := u₂
  e₁ := e₁
  e₂ := e₂
  m := m
  factorization₁ := factorization₁
  factorization₂ := factorization₂
  m_spec := m_spec

/-- The defining branch, factorization, and multiplicity conditions of chosen factorization
data. -/
theorem spec (D : Factorization A B a₁ a₂) :
    (∀ j : MaximalSpectrum B, j ∈ D.maximals) ∧
      (∀ j : MaximalSpectrum B, j.asIdeal.LiesOver (maximalIdeal A)) ∧
      (∀ j : MaximalSpectrum B,
        algebraMap B (Localization.AtPrime j.asIdeal) (algebraMap A B a₁) =
          (D.u₁ j : Localization.AtPrime j.asIdeal) * D.π j ^ D.e₁ j) ∧
      (∀ j : MaximalSpectrum B,
        algebraMap B (Localization.AtPrime j.asIdeal) (algebraMap A B a₂) =
          (D.u₂ j : Localization.AtPrime j.asIdeal) * D.π j ^ D.e₂ j) ∧
      (∀ j : MaximalSpectrum B, D.m j =
        (Module.length (Localization.AtPrime j.asIdeal)
          (Localization.AtPrime j.asIdeal ⧸ Ideal.span {D.π j})).toNat) := sorry

end Factorization

/-- The norm on residue-field units along a maximal branch of a finite local algebra. -/
noncomputable def residueNorm
    (A : Type u) {B : Type v} [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B]
    (j : MaximalSpectrum B) (h_liesOver : j.asIdeal.LiesOver (maximalIdeal A)) :
    j.asIdeal.ResidueFieldˣ →* (maximalIdeal A).ResidueFieldˣ :=
  -- Local instance justification (proof-local temporary data): use this supplied lying-over proof only for the selected branch.
  letI : j.asIdeal.LiesOver (maximalIdeal A) := h_liesOver
  -- Local instance justification (instance diamond): residue-field algebras depend on the chosen lying-over branch.
  letI : Algebra (maximalIdeal A).ResidueField j.asIdeal.ResidueField :=
    Ideal.ResidueField.algebraOfLiesOver (maximalIdeal A) j.asIdeal
  Units.map (Algebra.norm (maximalIdeal A).ResidueField)

namespace Factorization

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
variable [CommRing B] [Algebra A B] [Module.Finite A B]
variable {a₁ a₂ : A}

/-- The signed residue-unit term attached to one maximal branch. -/
def localTerm (D : Factorization A B a₁ a₂) (j : MaximalSpectrum B) :
    j.asIdeal.ResidueFieldˣ :=
  (-1 : j.asIdeal.ResidueFieldˣ) ^ (D.e₁ j * D.e₂ j) *
    Units.map (IsLocalRing.residue (Localization.AtPrime j.asIdeal)).toMonoidHom (D.u₁ j) ^
      D.e₂ j *
    Units.map (IsLocalRing.residue (Localization.AtPrime j.asIdeal)).toMonoidHom (D.u₂ j) ⁻¹ ^
      D.e₁ j

/-- The local term is the sign times the two residue units with the crossed exponents. -/
theorem localTerm_def (D : Factorization A B a₁ a₂) (j : MaximalSpectrum B) :
    D.localTerm j =
      (-1 : j.asIdeal.ResidueFieldˣ) ^ (D.e₁ j * D.e₂ j) *
        Units.map (IsLocalRing.residue (Localization.AtPrime j.asIdeal)).toMonoidHom (D.u₁ j) ^
          D.e₂ j *
        Units.map (IsLocalRing.residue (Localization.AtPrime j.asIdeal)).toMonoidHom (D.u₂ j) ⁻¹ ^
          D.e₁ j := sorry

/-- The factorization-dependent tame-symbol candidate in the residue field of the base. -/
noncomputable def value (D : Factorization A B a₁ a₂) :
    (maximalIdeal A).ResidueFieldˣ :=
  D.maximals.prod fun j ↦
    (TameSymbol.residueNorm A j (D.liesOver j) (D.localTerm j)) ^ D.m j

/-- The tame-symbol candidate is the product of the branch residue norms of the signed local
unit terms, with the principal-quotient lengths as outer exponents. -/
@[stacks 0EAQ "explicit norm-product formula for a tame symbol"]
theorem value_def (D : Factorization A B a₁ a₂) :
    D.value =
      D.maximals.prod fun j ↦
        (TameSymbol.residueNorm A j (D.liesOver j)
          ((-1 : j.asIdeal.ResidueFieldˣ) ^ (D.e₁ j * D.e₂ j) *
            Units.map (IsLocalRing.residue (Localization.AtPrime j.asIdeal)).toMonoidHom
                (D.u₁ j) ^ D.e₂ j *
            Units.map (IsLocalRing.residue (Localization.AtPrime j.asIdeal)).toMonoidHom
                (D.u₂ j) ⁻¹ ^ D.e₁ j)) ^ D.m j := sorry

end Factorization

end TameSymbol
