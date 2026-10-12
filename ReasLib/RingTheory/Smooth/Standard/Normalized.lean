/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.Smooth.Standard.Family

/-!
# Normalized standard-smooth presentations

This leaf gives finite-coordinate normal forms for submersive presentations.
The coordinate-free finite-family owner is `Standard.Family`.
-/

@[expose] public section

noncomputable section

universe u v w t

namespace Algebra

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]

/-- A prescribed finite family of relation positions can be extended to relation and variable
coordinates in which the distinguished-variable map is the left-summand inclusion. -/
@[stacks 07EY "submersive-presentation reindexing"]
theorem SubmersivePresentation.exists_reindex_extending
    {κ : Type*} [Finite κ] {ι : Type w} {σ : Type t} [Finite ι] [Finite σ]
    (P : SubmersivePresentation R A ι σ) (j : κ ↪ σ) :
    ∃ (τ : Type t) (υ : Type w) (_ : Finite τ) (_ : Finite υ)
      (f : κ ⊕ τ ≃ σ) (e : (κ ⊕ τ) ⊕ υ ≃ ι),
      (∀ k, f (.inl k) = j k) ∧ (P.reindex e f).map = Sum.inl := sorry

/-- A finite submersive presentation can be reindexed so a prescribed embedding
`Fin n ↪ σ` occupies the first relation positions and all distinguished variables form the
left summand `Fin c` of `Fin c ⊕ Fin m`. -/
@[stacks 07EY "normalized submersive presentation"]
theorem SubmersivePresentation.exists_finReindex_extending
    {ι : Type w} {σ : Type t} [Finite ι] [Finite σ]
    (P : SubmersivePresentation R A ι σ) {n : ℕ} (j : Fin n ↪ σ) :
    ∃ (c m : ℕ) (e : (Fin c ⊕ Fin m) ≃ ι) (f : Fin c ≃ σ) (h : n ≤ c),
      (∀ i, f (Fin.castLE h i) = j i) ∧ (P.reindex e f).map = Sum.inl := sorry

/-- Lemma 16.3.6: a finite family in a standard-smooth algebra can be placed
in the first distinguished coordinates of a finite submersive presentation.
The family may contain repeated values; only its coordinate positions need
to be distinct. -/
@[stacks 07EY "normalized prescribed-family presentation"]
theorem IsStandardSmooth.exists_finPresentation_containing
    {n : ℕ} [IsStandardSmooth R A] (beta : Fin n → A) :
    ∃ (c m : ℕ) (P : SubmersivePresentation R A (Fin c ⊕ Fin m) (Fin c)) (h : n ≤ c),
      P.map = Sum.inl ∧ ∀ i : Fin n, P.val (.inl (Fin.castLE h i)) = beta i := sorry

end Algebra
