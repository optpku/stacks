module

public import ReasLib.FieldTheory.Frobenius.Compositum
public import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Derivations over Frobenius composita

@stack 07P2

This leaf owns the coefficient-vanishing API for Frobenius composita.  It is independent of
p-bases and permits derivations valued in an arbitrary module.
-/

@[expose] public section

universe u v w

namespace FieldExtension.Frobenius

variable (p : ℕ) (k : Type u) {K : Type v}
variable [Field k] [Field K] [Algebra k K] [Fact p.Prime] [CharP K p]
variable {M : Type w} [AddCommGroup M] [Module K M] [Module k M]

/-- A `k`-derivation of `K` vanishes on the Frobenius compositum of `k` and `K^p`. -/
@[stacks 07P2 "derivations vanish on the Frobenius compositum"]
theorem Derivation.eq_zero_of_mem_compositum (theta : Derivation k K M) {a : K}
    (ha : a ∈ (compositum p k K : Set K)) : theta a = 0 := by
  change a ∈ IntermediateField.adjoin k (subfield p K : Set K) at ha
  refine IntermediateField.adjoin_induction
    (F := k) (s := (subfield p K : Set K))
    (p := fun x _ ↦ theta x = 0) ?_ ?_ ?_ ?_ ?_ ha
  · intro x hx
    obtain ⟨y, rfl⟩ := (mem_subfield_iff p K).mp hx
    rw [theta.leibniz_pow, ← Nat.cast_smul_eq_nsmul K,
      CharP.cast_eq_zero K p, zero_smul]
  · exact theta.map_algebraMap
  · intro x y _ _ hx hy
    simpa using congr_arg₂ (· + ·) hx hy
  · intro x _ hx
    simp [theta.leibniz_inv, hx]
  · intro x y _ _ hx hy
    simp [theta.leibniz, hx, hy]
/- Proof strategy: use `Derivation.leibniz_pow` to kill p-th powers in characteristic `p`, use
`Derivation.map_algebraMap` on the base field, and close the zero locus under the field operations
generating `IntermediateField.adjoin`. -/

end FieldExtension.Frobenius
