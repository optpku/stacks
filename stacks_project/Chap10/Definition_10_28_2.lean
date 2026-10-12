/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Ideal.Oka
import StacksCheckRecall

@[expose] public section

/-!
# Definition 10.28.2

@stack 05K9
-/

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 10.28.2: an Oka family of ideals of `R` is the canonical predicate
`Ideal.IsOka`, applied to the set family viewed as a predicate on ideals. The textbook clauses
`R ∈ 𝓕`, `(I : a) ∈ 𝓕`, and `(I, a) ∈ 𝓕` are exactly the fields `top` and `oka`, written in Lean
as `⊤ ∈ 𝓕`, `I.colon (Ideal.span {a}) ∈ 𝓕`, and `I ⊔ Ideal.span {a} ∈ 𝓕`. -/
@[stacks 05K9]
#check @Ideal.IsOka
