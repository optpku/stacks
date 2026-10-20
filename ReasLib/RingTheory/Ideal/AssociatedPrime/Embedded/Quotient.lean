/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.RingTheory.Spectrum.Prime.Module
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Ideal.AssociatedPrime.Embedded

@[expose] public section

/-!
# Removing Embedded Associated Primes

@stack 02M6

This leaf owns the canonical largest submodule with nowhere-dense support and
the embedded-prime-free quotient it determines.
-/

universe u v

open PrimeSpectrum TopologicalSpace

namespace Module

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The elements whose cyclic support lies in the union of the zero loci of the embedded
associated primes of `M`. -/
@[stacks 02M6 "canonical nowhere-dense submodule"]
def embeddedPrimeFreeSubmodule : Submodule R M where
  carrier := {m | Module.support R (R ∙ m) ⊆
    ⋃ p ∈ embeddedAssociatedPrimes R M, PrimeSpectrum.zeroLocus p}
  zero_mem' := sorry
  add_mem' := sorry
  smul_mem' := sorry

namespace embeddedPrimeFreeSubmodule

/-- Membership in the canonical submodule is the source cyclic-support condition. -/
@[stacks 02M6 "membership in the canonical nowhere-dense submodule"]
theorem mem_iff (m : M) :
    m ∈ embeddedPrimeFreeSubmodule R M ↔
      Module.support R (R ∙ m) ⊆
        ⋃ p ∈ embeddedAssociatedPrimes R M, PrimeSpectrum.zeroLocus p := Iff.rfl

variable [IsNoetherianRing R] [Module.Finite R M]

/-- The canonical submodule is maximal among submodules whose relative support is nowhere dense
in the support of `M`. -/
@[stacks 02M6 "maximal nowhere-dense submodule"]
theorem isMaximal_nowhereDense :
    Maximal
      (fun K : Submodule R M ↦
        IsNowhereDense
          {p : Module.support R M | (p : PrimeSpectrum R) ∈ Module.support R K})
      (embeddedPrimeFreeSubmodule R M) := sorry

/-- Quotienting by the canonical submodule preserves support. -/
@[stacks 02M6 "support of the embedded-prime-free quotient"]
theorem support_quotient :
    Module.support R (M ⧸ embeddedPrimeFreeSubmodule R M) = Module.support R M := sorry

/-- The quotient by the canonical submodule has no embedded associated primes. -/
@[stacks 02M6 "embedded associated primes of the quotient"]
theorem embeddedAssociatedPrimes_quotient :
    embeddedAssociatedPrimes R (M ⧸ embeddedPrimeFreeSubmodule R M) = ∅ := sorry

/-- Away from an element contained in every embedded associated prime, the quotient map becomes
an isomorphism after localization. -/
@[stacks 02M6 "localization of the embedded-prime-free quotient map"]
theorem localized_quotientMap_bijective (f : R)
    (hf : ∀ p ∈ embeddedAssociatedPrimes R M, f ∈ p) :
    Function.Bijective
      (LocalizedModule.map (.powers f) (embeddedPrimeFreeSubmodule R M).mkQ) := sorry

end embeddedPrimeFreeSubmodule
end Module
