module

public import ReasLib.FieldTheory.PBasis
import Mathlib.Order.Zorn
import Mathlib.Tactic.CrossRefAttribute

/-!
# Existence and extension of p-bases

@stack 07P2

The index of a p-basis is an implementation choice, so the public surface exposes extension and
existence propositions rather than a chosen family or a witness package.
-/

@[expose] public section

universe u v w

namespace FieldExtension.PBasis

section Extension

variable (p : ℕ) (k : Type u) {K : Type v}
variable [Field k] [Field K] [Algebra k K] [Fact p.Prime] [CharP K p]
variable {ι : Type w}

/-- Lemma 15.46.2, extension conclusion: a p-independent family can be enlarged to a p-basis
without changing its indexed subfamily. -/
@[stacks 07P2 "Lemma 15.46.2, extension of a p-independent family to a p-basis"]
theorem exists_extension (x : ι → K) (hx : IsIndependent p k x) :
    ∃ (ι' : Type (max v w)) (y : ι' → K) (e : ι ↪ ι'),
      (∀ i, y (e i) = x i) ∧ IsBasis p k y := sorry
/- Proof strategy: use a Zorn maximality argument for p-independent families and the
`adjoin_eq_top` criterion for maximality; keep the extension index as explicit data. -/

end Extension

section Existence

variable (p : ℕ) (k : Type u) (K : Type v)
variable [Field k] [Field K] [Algebra k K] [Fact p.Prime] [CharP K p]

/-- Lemma 15.46.2, existence conclusion: every characteristic-`p` field extension admits a
p-basis. -/
@[stacks 07P2 "Lemma 15.46.2, existence of a p-basis"]
theorem exists_basis : ∃ (ι : Type v) (x : ι → K), IsBasis p k x := sorry
/- Proof strategy: apply `exists_extension` to the empty family and lower the resulting index to
the universe of `K` using the standard cardinal bound for a family of field elements. -/

end Existence

end FieldExtension.PBasis
