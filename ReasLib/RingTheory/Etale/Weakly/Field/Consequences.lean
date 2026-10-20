/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Etale.Weakly.Field
import Mathlib.Tactic.CrossRefAttribute

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
theorem isIntegral (h : Algebra.WeaklyEtale K B) : Algebra.IsIntegral K B := sorry

/-- Lemma 15.106.1 (3), Stacks `0CKR`: every finitely generated subalgebra is a finite product
of finite separable field extensions. -/
@[stacks 0CKR "(3), finite-product description of finitely generated subalgebras"]
theorem exists_algEquiv_prod_of_fg_subalgebra
    (h : Algebra.WeaklyEtale K B) (A : Subalgebra K B) (hA : A.FG) :
    ∃ (I : Type u) (_ : Finite I) (L : I → Type u) (_ : ∀ i, Field (L i))
      (_ : ∀ i, Algebra K (L i)) (_ : A ≃ₐ[K] Π i, L i),
      ∀ i, Module.Finite K (L i) ∧ Algebra.IsSeparable K (L i) := sorry

/-- Lemma 15.106.1 (4), Stacks `0CKR`: a nonzero weakly etale algebra over a field is a field
exactly when all of its idempotents are trivial. -/
@[stacks 0CKR "(4), field criterion by idempotents"]
theorem isField_iff_idempotents [Nontrivial B] (h : Algebra.WeaklyEtale K B) :
    IsField B ↔ ∀ e : B, IsIdempotentElem e → e = 0 ∨ e = 1 := sorry

/-- Lemma 15.106.1 (5), Stacks `0CKR`: when a weakly etale algebra over a field is itself a
field, it is a separable algebraic extension. -/
@[stacks 0CKR "(5), separability in the field case"]
theorem isSeparable_of_isField
    (h : Algebra.WeaklyEtale K B) (hB : IsField B) : Algebra.IsSeparable K B := sorry

/-- Lemma 15.106.1 (6), Stacks `0CKR`: every subalgebra of a weakly etale algebra over a field is
weakly etale. -/
@[stacks 0CKR "(6), subalgebras"]
theorem subalgebra (h : Algebra.WeaklyEtale K B) (A : Subalgebra K B) :
    Algebra.WeaklyEtale K A := sorry

/-- Lemma 15.106.1 (7), Stacks `0CKR`: every quotient algebra of a weakly etale algebra over a
field is weakly etale. -/
@[stacks 0CKR "(7), quotient algebras"]
theorem quotient (h : Algebra.WeaklyEtale K B) (I : Ideal B) :
    Algebra.WeaklyEtale K (B ⧸ I) := sorry

/-- Lemma 15.106.1 (8), Stacks `0CKR`: the tensor product of two weakly etale algebras over a
field is weakly etale. -/
@[stacks 0CKR "(8), tensor products"]
theorem tensorProduct {B' : Type u} [CommRing B'] [Algebra K B']
    (hB : Algebra.WeaklyEtale K B) (hB' : Algebra.WeaklyEtale K B') :
    Algebra.WeaklyEtale K (B ⊗[K] B') := sorry

end Algebra.WeaklyEtale
