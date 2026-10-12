/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.GradedAlgebra.Irrelevant
import StacksCheckRecall

@[expose] public section

open scoped HomogeneousIdeal

universe u v

section

variable {S : Type u} [CommRing S]
variable {σ : Type v} [SetLike σ S] [AddSubgroupClass σ S]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable (s : Set S)
variable (hs : ∀ ⦃x⦄, x ∈ s → ∃ n > 0, x ∈ 𝒜 n)

/-!
Lemma 10.58.1: positive-degree homogeneous elements generate the
graded ring over its degree-zero part exactly when they generate the
irrelevant ideal.

@stack 07Z4
-/
@[stacks 07Z4]
#check (HomogeneousIdeal.adjoin_eq_top_iff_span_eq_irrelevant
    (𝒜 := 𝒜) (s := s) hs :
  Algebra.adjoin (𝒜 0) s = ⊤ ↔ Ideal.span s = 𝒜₊.toIdeal)

#check (HomogeneousIdeal.span_le_irrelevant (𝒜 := 𝒜) (s := s) hs :
  Ideal.span s ≤ 𝒜₊.toIdeal)

#check (HomogeneousIdeal.adjoin_eq_top_iff_irrelevant_le_span
    (𝒜 := 𝒜) (s := s) hs :
  Algebra.adjoin (𝒜 0) s = ⊤ ↔ 𝒜₊.toIdeal ≤ Ideal.span s)

end
