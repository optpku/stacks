/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.Weakly.Field
import ReasLib.RingTheory.AbsolutelyFlat
import ReasLib.RingTheory.Etale.Weakly.Operations
import Mathlib.Tactic.CrossRefAttribute
import Mathlib.Tactic.Ring

/-!
# Consequences of weak etaleness over a field

Weakly etale algebras over a field are integral and are built from finite separable extensions.
The property is inherited by subalgebras and quotients and is preserved by tensor products.

@stack 0CKR
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Algebra.WeaklyEtale

variable {K B : Type u} [Field K] [CommRing B] [Algebra K B]

/-- Lemma 15.106.1 (2), Stacks `0CKR`: a weakly etale algebra over a field is integral. -/
@[stacks 0CKR "(2), integrality over the base field"]
theorem isIntegral (h : Algebra.WeaklyEtale K B) : Algebra.IsIntegral K B := by
  refine ⟨fun b ↦ ?_⟩
  let A := Algebra.adjoin K ({b} : Set B)
  have hA : A.FG := ⟨{b}, by simp [A]⟩
  letI : Algebra.Etale K A := etale_of_fg_subalgebra h A hA
  letI : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A
  exact (_root_.IsIntegral.of_finite K (⟨b, Algebra.subset_adjoin (by simp)⟩ : A)).map A.val

/-- Lemma 15.106.1 (3), Stacks `0CKR`: every finitely generated subalgebra is a finite product
of finite separable field extensions. -/
@[stacks 0CKR "(3), finite-product description of finitely generated subalgebras"]
theorem exists_algEquiv_prod_of_fg_subalgebra
    (h : Algebra.WeaklyEtale K B) (A : Subalgebra K B) (hA : A.FG) :
    ∃ (I : Type u) (_ : Finite I) (L : I → Type u) (_ : ∀ i, Field (L i))
      (_ : ∀ i, Algebra K (L i)) (_ : A ≃ₐ[K] Π i, L i),
      ∀ i, Module.Finite K (L i) ∧ Algebra.IsSeparable K (L i) := by
  exact (Algebra.Etale.iff_exists_algEquiv_prod K A).mp (etale_of_fg_subalgebra h A hA)

private theorem exists_sq_mul_of_etale (h : Algebra.Etale K B) (b : B) :
    ∃ c : B, b = b ^ 2 * c := by
  classical
  obtain ⟨I, _, L, _, _, e, _⟩ := (Algebra.Etale.iff_exists_algEquiv_prod K B).mp h
  refine ⟨e.symm (fun i ↦ (e b i)⁻¹), e.injective ?_⟩
  ext i
  by_cases hi : e b i = 0 <;> simp [hi, pow_two, mul_assoc]

/-- Lemma 15.106.1 (4), Stacks `0CKR`: a nonzero weakly etale algebra over a field is a field
exactly when all of its idempotents are trivial. -/
@[stacks 0CKR "(4), field criterion by idempotents"]
theorem isField_iff_idempotents [Nontrivial B] (h : Algebra.WeaklyEtale K B) :
    IsField B ↔ ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1 := by
  classical
  constructor
  · intro hB
    letI := hB.isDomain
    exact fun _ he ↦ IsIdempotentElem.iff_eq_zero_or_one.mp he
  · intro hid
    refine ⟨exists_pair_ne B, mul_comm, fun {b} hb ↦ ?_⟩
    let A := Algebra.adjoin K ({b} : Set B)
    have hA : A.FG := ⟨{b}, by simp [A]⟩
    let a : A := ⟨b, Algebra.subset_adjoin (by simp)⟩
    obtain ⟨c, hac⟩ := exists_sq_mul_of_etale (etale_of_fg_subalgebra h A hA) a
    have hbc : b = b ^ 2 * (c : B) := congrArg (fun x : A ↦ (x : B)) hac
    have he : IsIdempotentElem (b * (c : B)) := by
      change (b * (c : B)) * (b * (c : B)) = b * (c : B)
      calc
        (b * (c : B)) * (b * (c : B)) = (b ^ 2 * (c : B)) * (c : B) := by ring
        _ = b * (c : B) := by rw [← hbc]
    rcases hid _ he with he | he
    · exfalso
      apply hb
      calc
        b = b ^ 2 * (c : B) := hbc
        _ = b * (b * (c : B)) := by ring
        _ = 0 := by rw [he, mul_zero]
    · exact ⟨c, he⟩

/-- Lemma 15.106.1 (5), Stacks `0CKR`: when a weakly etale algebra over a field is itself a
field, it is a separable algebraic extension. -/
@[stacks 0CKR "(5), separability in the field case"]
theorem isSeparable_of_isField
    (h : Algebra.WeaklyEtale K B) (hB : IsField B) : Algebra.IsSeparable K B := by
  letI := hB.toField
  refine ⟨fun b ↦ ?_⟩
  let A := Algebra.adjoin K ({b} : Set B)
  have hA : A.FG := ⟨{b}, by simp [A]⟩
  letI : Algebra.Etale K A := etale_of_fg_subalgebra h A hA
  letI : Module.Finite K A := Algebra.FormallyUnramified.finite_of_free K A
  letI := fieldOfFiniteDimensional K A
  letI : Algebra.IsSeparable K A := Algebra.FormallyUnramified.isSeparable K A
  exact (Algebra.IsSeparable.isSeparable K
    (⟨b, Algebra.subset_adjoin (by simp)⟩ : A)).map A.val Subtype.val_injective

/-- Lemma 15.106.1 (6), Stacks `0CKR`: every subalgebra of a weakly etale algebra over a field is
weakly etale. -/
@[stacks 0CKR "(6), subalgebras"]
theorem subalgebra (h : Algebra.WeaklyEtale K B) (A : Subalgebra K B) :
    Algebra.WeaklyEtale K A := by
  -- Every element of A has its von Neumann regular factorization in K[a] ⊆ A.
  letI : IsAbsolutelyFlatRing A := by
    refine ⟨fun a ↦ ?_⟩
    let S := Algebra.adjoin K ({(a : B)} : Set B)
    have hS : S.FG := ⟨{(a : B)}, by simp [S]⟩
    have hSA : S ≤ A := Algebra.adjoin_le (by simpa using a.property)
    obtain ⟨c, hc⟩ := exists_sq_mul_of_etale (etale_of_fg_subalgebra h S hS)
      (⟨a, Algebra.subset_adjoin (by simp)⟩ : S)
    refine ⟨⟨c, hSA c.property⟩, Subtype.ext ?_⟩
    exact congrArg (fun x : S ↦ (x : B)) hc
  letI : Algebra.IsIntegral K B := isIntegral h
  letI : Algebra.IsIntegral A B :=
    ⟨fun b ↦ (Algebra.IsIntegral.isIntegral (R := K) b).tower_top⟩
  -- The integral inclusion A → B is faithfully flat, so weak etaleness descends.
  letI : Module.FaithfullyFlat A B := by
    apply Module.FaithfullyFlat.of_comap_surjective
    intro p
    letI : p.asIdeal.IsPrime := p.isPrime
    obtain ⟨q, _, hq, hqp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p.asIdeal
      (⊥ : Ideal B) (by simp [← RingHom.ker_eq_comap_bot])
    exact ⟨⟨q, hq⟩, PrimeSpectrum.ext hqp⟩
  exact of_faithfullyFlat (RingHom.faithfullyFlat_algebraMap_iff.mpr inferInstance) h

/-- Lemma 15.106.1 (7), Stacks `0CKR`: every quotient algebra of a weakly etale algebra over a
field is weakly etale. -/
@[stacks 0CKR "(7), quotient algebras"]
theorem quotient (h : Algebra.WeaklyEtale K B) (I : Ideal B) :
    Algebra.WeaklyEtale K (B ⧸ I) := by
  letI : Algebra.WeaklyEtale K B := h
  letI : Module.Flat B (B ⧸ I) :=
    Module.Flat.of_flat_base_and_flat_tensorSquareMultiplication
      (tensorSquare_flat h) (Module.Flat.of_free : Module.Flat K (B ⧸ I))
  letI : Algebra.WeaklyEtale B (B ⧸ I) :=
    { flat_lmul' := RingHom.Flat.of_bijective
        (LinearMap.mul'_bijective_of_surjective B (B ⧸ I) Ideal.Quotient.mk_surjective) }
  exact Algebra.WeaklyEtale.trans K B (B ⧸ I)

/-- Lemma 15.106.1 (8), Stacks `0CKR`: the tensor product of two weakly etale algebras over a
field is weakly etale. -/
@[stacks 0CKR "(8), tensor products"]
theorem tensorProduct {B' : Type u} [CommRing B'] [Algebra K B']
    (hB : Algebra.WeaklyEtale K B) (hB' : Algebra.WeaklyEtale K B') :
    Algebra.WeaklyEtale K (B ⊗[K] B') := by
  letI : Algebra.WeaklyEtale K B := hB
  letI : Algebra.WeaklyEtale K B' := hB'
  exact Algebra.WeaklyEtale.trans K B (B ⊗[K] B')

end Algebra.WeaklyEtale
