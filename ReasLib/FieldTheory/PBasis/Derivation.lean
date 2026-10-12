/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.FieldTheory.PBasis
public import ReasLib.FieldTheory.Frobenius.Derivation
import ReasLib.FieldTheory.PBasis.Existence
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derivations dual to p-independent families

@stack 07P2

This leaf owns the derivation criterion for p-independence. Coefficient vanishing is supplied by
the neutral Frobenius derivation owner, while the forward construction may extend a p-independent
family to a p-basis. No Kähler differential module occurs in this API.
-/

@[expose] public section

universe u v w

namespace FieldExtension.PBasis

open FieldExtension.Frobenius

variable (p : ℕ) (k : Type u) {K : Type v}
variable [Field k] [Field K] [Algebra k K] [Fact p.Prime] [CharP K p]
variable {ι : Type w}

/-- Derivations separating the members of a family force its restricted monomials to be linearly
independent over the Frobenius compositum. -/
@[stacks 07P2 "dual derivations imply p-independence"]
theorem isIndependent_of_dual_derivations (x : ι → K)
    (hdual : ∀ i, ∃ θ : Derivation k K K,
      θ (x i) = 1 ∧ ∀ j, j ≠ i → θ (x j) = 0) :
    IsIndependent p k x := sorry
/- Proof strategy: choose a nontrivial restricted-monomial relation of minimal total exponent,
differentiate at a positive exponent using the corresponding dual derivation, note that derivations
kill the coefficients with `FieldExtension.Frobenius.Derivation.eq_zero_of_mem_compositum`, and
lower that exponent to contradict minimality. -/

/-- A p-independent family has a derivation dual to each one of its members. -/
@[stacks 07P2 "dual derivation from p-independence"]
theorem IsIndependent.exists_dual_derivation {x : ι → K} (hx : IsIndependent p k x) (i : ι) :
    ∃ θ : Derivation k K K,
      θ (x i) = 1 ∧ ∀ j, j ≠ i → θ (x j) = 0 := sorry
/- Proof strategy: extend `x` to a p-basis with `exists_extension`, define the coordinate
derivation on the restricted-monomial basis, and restrict the resulting identities along the
embedding of the original family. -/

/-- A family is p-independent exactly when each member admits a derivation dual to the family. -/
@[stacks 07P2 "p-independence via dual derivations"]
theorem isIndependent_iff_dual_derivations (x : ι → K) :
    IsIndependent p k x ↔
      ∀ i, ∃ θ : Derivation k K K,
        θ (x i) = 1 ∧ ∀ j, j ≠ i → θ (x j) = 0 := by
  constructor
  · intro hx i
    exact IsIndependent.exists_dual_derivation p k hx i
  · exact isIndependent_of_dual_derivations p k x
/- Proof strategy: collect `IsIndependent.exists_dual_derivation` for the forward implication and
apply `isIndependent_of_dual_derivations` for the reverse implication. -/

end FieldExtension.PBasis
