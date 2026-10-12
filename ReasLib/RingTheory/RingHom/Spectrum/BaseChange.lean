/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.Fiber.BaseChange
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Base change of surjective maps on prime spectra

This leaf records the tensor-product base-change stability of surjectivity for
the canonical map on prime spectra. It is independent of any specific
criterion used to establish the original surjectivity.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace PrimeSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- If `Spec(S) → Spec(R)` is surjective, then its arbitrary tensor-product base change is
surjective. -/
@[stacks 00FI]
theorem comap_surjective_baseChange
    {R' : Type w} [CommRing R'] [Algebra R R']
    (h : Function.Surjective (comap (algebraMap R S))) :
    Function.Surjective (comap (algebraMap R' (R' ⊗[R] S))) := sorry

end PrimeSpectrum
