/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Spectrum.Prime.Module
import Mathlib.Tactic.CrossRefAttribute

/-!
@stack 05GE
-/

/-!
# Residue-field fibers of module support

`Ideal.Fiber p M` is Mathlib's canonical model for the residue-field fiber
`κ(p) ⊗[R] M`.  This leaf gives the short support API used by map loci; it is
kept separate from the linear-map layer so other support arguments can reuse it
without importing any map-specific declarations.
-/

@[expose] public section

universe u v

open PrimeSpectrum
open scoped TensorProduct

namespace Module

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/-- A finite module is nontrivial at `p` exactly when its canonical residue-field fiber is nontrivial. -/
@[stacks 05GE "support detected by the residue-field fiber"]
theorem mem_support_iff_nontrivial_fiber [Module.Finite R M]
    (p : PrimeSpectrum R) :
    p ∈ Module.support R M ↔ Nontrivial (p.asIdeal.Fiber M) := sorry

/-- A finite module is outside support at `p` exactly when its canonical residue-field fiber is
subsingleton.  The negative form is the one needed for cokernel surjectivity loci. -/
@[stacks 05GE "support complement detected by the residue-field fiber"]
theorem notMem_support_iff_subsingleton_fiber [Module.Finite R M]
    (p : PrimeSpectrum R) :
    p ∉ Module.support R M ↔ Subsingleton (p.asIdeal.Fiber M) := sorry

end Module

namespace LocalizedModule.AtPrime

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

/- The support criterion is deliberately exposed at the localization owner: callers that already
  have a localized module should not rebuild the support argument or introduce a local instance. -/
/-- For a finite module over a prime ideal, localization vanishes exactly when
the residue-field fiber vanishes. -/
@[stacks 05GE "ideal-level localization and residue-field fiber vanishing"]
theorem subsingleton_iff_residueFiber [Module.Finite R M] (p : Ideal R) [p.IsPrime] :
    Subsingleton (LocalizedModule.AtPrime p M) ↔
      Subsingleton (p.ResidueField ⊗[R] M) := sorry

/-- For a finite module, vanishing at a prime is equivalent to vanishing of its residue-field
fiber. -/
@[stacks 05GE "localization and residue-field fiber vanishing"]
theorem subsingleton_iff_fiber [Module.Finite R M] (p : PrimeSpectrum R) :
    Subsingleton (LocalizedModule.AtPrime p.asIdeal M) ↔
      Subsingleton (p.asIdeal.Fiber M) := sorry

end LocalizedModule.AtPrime
