/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

open scoped TensorProduct
open Algebra.TensorProduct

universe u v w

namespace FieldExtension

variable {k : Type u} {E : Type v} {F : Type w} [Field k] [Field E] [Field F]
variable [Algebra k E] [Algebra k F]

/-- Lemma 9.6.9 (Tag 0H7K): any two field extensions `E/k` and `F/k` embed into a common
overfield of `k`. -/
theorem existsCommonOverfield :
    ∃ (M : Type (max v w)) (_ : Field M) (_ : Algebra k M) (iE : E →ₐ[k] M) (iF : F →ₐ[k] M),
      Function.Injective iE ∧ Function.Injective iF := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (E ⊗[k] F)
  let M : Type (max v w) := (E ⊗[k] F) ⧸ m
  -- Local instance justification (proof-local temporary data): the selected maximal ideal supplies the quotient-field structure only while constructing the existential witness.
  letI : m.IsMaximal := hm
  -- Local instance justification (proof-local temporary data): the quotient field is used only to produce the common overfield and its two embedding maps.
  letI : Field M := Ideal.Quotient.field m
  refine ⟨M, inferInstance, inferInstance, (Ideal.Quotient.mkₐ k m).comp includeLeft,
    (Ideal.Quotient.mkₐ k m).comp includeRight, RingHom.injective _, RingHom.injective _⟩

end FieldExtension
