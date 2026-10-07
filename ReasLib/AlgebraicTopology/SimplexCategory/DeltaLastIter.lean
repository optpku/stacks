module

public import Mathlib.AlgebraicTopology.SimplexCategory.DeltaZeroIter
public import Mathlib.AlgebraicTopology.SimplexCategory.Rev

/-!
# Iterated final faces and degeneracies in the simplex category

This file is the order-reversed counterpart of Mathlib's `DeltaZeroIter`.  It exposes the
iterations of the final coface and codegeneracy maps directly, so constructions based at the
final vertex do not have to repeatedly unfold `SimplexCategory.rev`.
-/

@[expose] public section

open CategoryTheory Simplicial

namespace SimplexCategory

/-- If `n + i = m`, the `i`-fold iteration of the final coface map from `⦋n⦌` to `⦋m⦌`. -/
@[stacks 08ND "iterated final coface map"]
def δLastIter (i : ℕ) {n m : ℕ} (hi : n + i = m) : ⦋n⦌ ⟶ ⦋m⦌ :=
  rev.map (δ₀Iter i hi)

/-- If `n + i = m`, the `i`-fold iteration of the final codegeneracy map from `⦋m⦌` to
`⦋n⦌`. -/
@[stacks 08ND "iterated final codegeneracy map"]
def σLastIter (i : ℕ) {n m : ℕ} (hi : n + i = m) : ⦋m⦌ ⟶ ⦋n⦌ :=
  rev.map (σ₀Iter i hi)

/-- Reversing an iterated final coface gives the corresponding iterated initial coface. -/
@[simp, stacks 08ND "reversal of an iterated final coface"]
theorem rev_map_δLastIter (i : ℕ) {n m : ℕ} (hi : n + i = m) :
    rev.map (δLastIter i hi) = δ₀Iter i hi := sorry

/-- Reversing an iterated final codegeneracy gives the corresponding iterated initial
codegeneracy. -/
@[simp, stacks 08ND "reversal of an iterated final codegeneracy"]
theorem rev_map_σLastIter (i : ℕ) {n m : ℕ} (hi : n + i = m) :
    rev.map (σLastIter i hi) = σ₀Iter i hi := sorry

/-- Iterating the final coface zero times gives the identity. -/
@[simp]
theorem δLastIter_zero (n : ℕ) : δLastIter 0 (add_zero n) = 𝟙 _ := sorry

/-- Iterating the final coface once gives the final coface. -/
@[simp]
theorem δLastIter_one (n : ℕ) :
    δLastIter 1 (n := n) rfl = δ (Fin.last (n + 1)) := sorry

/-- Iterating the final codegeneracy zero times gives the identity. -/
@[simp]
theorem σLastIter_zero (n : ℕ) : σLastIter 0 (add_zero n) = 𝟙 _ := sorry

/-- Iterating the final codegeneracy once gives the final codegeneracy. -/
@[simp]
theorem σLastIter_one (n : ℕ) :
    σLastIter 1 (n := n) rfl = σ (Fin.last n) := sorry

/-- An iterated final coface followed by the matching final codegeneracy is the identity. -/
@[reassoc (attr := simp), stacks 08ND "iterated final coface-codegeneracy identity"]
theorem δLastIter_σLastIter (i : ℕ) {n m : ℕ} (hi : n + i = m) :
    δLastIter i hi ≫ σLastIter i hi = 𝟙 _ := sorry

/-- An iterated final coface is a monomorphism. -/
instance (i : ℕ) {n m : ℕ} (hi : n + i = m) : Mono (δLastIter i hi) := sorry

/-- An iterated final codegeneracy is an epimorphism. -/
instance (i : ℕ) {n m : ℕ} (hi : n + i = m) : Epi (σLastIter i hi) := sorry

end SimplexCategory
