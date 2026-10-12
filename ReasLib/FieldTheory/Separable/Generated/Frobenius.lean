/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.Separable.Generated

@[expose] public section

/-!
# Frobenius Criteria for Separably Generated Extensions

This leaf records the characteristic-`p` Frobenius linear-independence criterion in the
project-level `Algebra.IsSeparablyGenerated` interface.  The underlying construction of a
separating transcendence basis is provided by Mathlib.

@stack 030W
-/

universe u v

namespace IntermediateField

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- Tag 030W: if the `p`-th-power map preserves `k`-linear independence of every finite
subset of an ambient field, then it preserves that independence on every intermediate field. -/
@[stacks 030W "intermediate-field restriction"]
theorem linearIndepOn_pow_of_ambient
    {p : ℕ}
    (hpow : ∀ s : Finset K,
      LinearIndepOn k _root_.id (s : Set K) →
        LinearIndepOn k (fun x ↦ x ^ p) (s : Set K))
    (L : IntermediateField k K) :
    ∀ s : Finset L,
      LinearIndepOn k _root_.id (s : Set L) →
        LinearIndepOn k (fun x ↦ x ^ p) (s : Set L) := sorry

end IntermediateField

namespace Algebra

namespace IsSeparablyGenerated

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]

/-- Tag 030W: the Frobenius linear-independence criterion makes a finitely generated
characteristic-`p` field extension separably generated.  This packages Mathlib's
separating-transcendence-basis theorem as an `Algebra.IsSeparablyGenerated` witness. -/
@[stacks 030W "(2) ⇒ (1) finitely generated case"]
theorem of_linearIndepOn_pow
    {p : ℕ} [Fact p.Prime] [CharP k p] [EssFiniteType k K]
    (hlin : ∀ s : Finset K,
      LinearIndepOn k _root_.id (s : Set K) →
        LinearIndepOn k (fun x ↦ x ^ p) (s : Set K)) :
    IsSeparablyGenerated k K := sorry

end IsSeparablyGenerated

end Algebra
