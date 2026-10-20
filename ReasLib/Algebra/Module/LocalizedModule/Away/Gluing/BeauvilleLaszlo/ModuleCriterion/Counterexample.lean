module

public import ReasLib.Algebra.Module.LocalizedModule.Away.Gluing.BeauvilleLaszlo.ModuleCriterion.Consequences
public import ReasLib.RingTheory.Ideal.Principal

import Mathlib.Tactic.CrossRefAttribute

/-!
# Quotient-module obstructions to Beauville-Laszlo glueability

An explicit nonzero quotient class which is killed by a power of `f` and vanishes after tensoring
with the principal-adic completion obstructs module glueability.  This is the algebraic core of the
smooth-germ counterexample in Example 15.91.12.

@stack 0BNY
-/

@[expose] public section

noncomputable section

universe u

namespace LocalizedModule.Away.BeauvilleLaszlo

variable {R : Type u} [CommRing R]
variable {f φ : R}

/-- The quotient class of `ψ` belongs to the `f`-primary component of `R ⨸ (φ)` when
`f * ψ = φ`. -/
@[stacks 0BNY "the quotient torsion class"]
theorem quotientMk_mem_principalPrimaryComponent {ψ : R} (hmul : f * ψ = φ) :
    Ideal.Quotient.mk (principalIdeal φ) ψ ∈
      (principalIdeal f).primaryComponent (R ⧸ principalIdeal φ) := sorry

/-- The explicit `f`-power-torsion witness represented by `ψ` in `R ⨸ (φ)`. -/
@[stacks 0BNY "the quotient torsion witness"]
abbrev quotientPrimaryComponentWitness {ψ : R} (hmul : f * ψ = φ) :
    (principalIdeal f).primaryComponent (R ⧸ principalIdeal φ) :=
  ⟨Ideal.Quotient.mk (principalIdeal φ) ψ,
    quotientMk_mem_principalPrimaryComponent hmul⟩

/-- The quotient torsion witness is nonzero whenever its underlying quotient class is nonzero. -/
@[stacks 0BNY "nonvanishing of the quotient torsion witness"]
theorem quotientPrimaryComponentWitness_ne_zero {ψ : R} (hmul : f * ψ = φ)
    (hψ_ne : Ideal.Quotient.mk (principalIdeal φ) ψ ≠ 0) :
    quotientPrimaryComponentWitness hmul ≠ 0 := sorry

/-- Example 15.91.12 (Non glueable module): if `f * ψ = φ`, the class of `ψ` in
`R ⨸ (φ)` is nonzero, and its explicit `f`-power-torsion witness vanishes after tensoring
with the principal-adic completion, then `R ⨸ (φ)` is not Beauville-Laszlo glueable.  In the
smooth-germ example, `f(x) = x`, `φ(x) = exp(-1 / x ^ 2)`, and `ψ = φ / f`. -/
@[stacks 0BNY "Example 15.91.12 (Non glueable module)"]
theorem quotient_notGlueableAlong_principalAdicCompletion_of_witness
    {ψ : R} (hmul : f * ψ = φ)
    (hψ_ne : Ideal.Quotient.mk (principalIdeal φ) ψ ≠ 0)
    (hcompletion : completionFPowerTorsionToCompletionTensor
      (R ⧸ principalIdeal φ) f (quotientPrimaryComponentWitness hmul) = 0) :
    ¬ (beauvilleLaszloModuleCechSequence
      (principalAdicCompletion f) (R ⧸ principalIdeal φ) f).ShortExact := sorry

end LocalizedModule.Away.BeauvilleLaszlo
