module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.Tactic.CrossRefAttribute

/-!
# Hilbert--Samuel functions

@stack 07DU

This leaf owns the length-valued Hilbert--Samuel functions independently of any particular
chapter proof.  The values are in `ℕ∞`, which keeps the definitions total; finiteness hypotheses
are imposed only by the theorems that convert them to ordinary natural or rational polynomials.
-/

@[expose] public section

universe u v

open scoped Pointwise

namespace Ideal

variable {R : Type u} [CommRing R]
variable (I : Ideal R) (M : Type v) [AddCommGroup M] [Module R M]

/-- Definition 10.59.1 (Tag 07DU): the length of `M / I^(n+1)M`. -/
@[stacks 07DU "Hilbert-Samuel chi function"]
noncomputable def hilbertSamuelChi (n : ℕ) : ℕ∞ :=
  Module.length R (M ⧸ (I ^ (n + 1) • ⊤ : Submodule R M))

/-- Definition 10.59.1 (Tag 07DU): the length of the graded quotient `I^n M / I^(n+1)M`. -/
@[stacks 07DU "Hilbert-Samuel phi function"]
noncomputable def hilbertSamuelPhi (n : ℕ) : ℕ∞ :=
  Module.length R
    ((I ^ n • ⊤ : Submodule R M) ⧸ (I • ⊤ : Submodule R (I ^ n • ⊤ : Submodule R M)))

end Ideal

/-- Source notation for `Ideal.hilbertSamuelChi`.

The function name is already carried by the ideal and module arguments, so the reusable
notation is the bare Greek letter; an underscore is not part of the API. -/
scoped[Ideal] prefix:max "χ" => Ideal.hilbertSamuelChi

/-- Source notation for `Ideal.hilbertSamuelPhi`.

The function name is already carried by the ideal and module arguments, so the reusable
notation is the bare Greek letter; an underscore is not part of the API. -/
scoped[Ideal] prefix:max "φ" => Ideal.hilbertSamuelPhi
