/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.RingTheory.Spectrum.Prime.DirectLimit.Surjective
import StacksCheckRecall

@[expose] public section

universe u v

namespace Ring.DirectLimit

variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
variable (A : ι → Type v) [∀ i, CommRing (A i)]
variable (f : ∀ i j, i ≤ j → A i →+* A j) [DirectedSystem A (f · · ·)]

/- Exercise 111.2.5: if `ι` is a directed set and `(A, f)` is a directed system of
commutative rings with colimit `Ring.DirectLimit A (f · · ·)`, and if
`PrimeSpectrum.comap (f i j hij)` is surjective for all `i ≤ j`, then
`PrimeSpectrum.comap (of A (f · · ·) i)` is surjective for every stage `i`. -/
@[stacks 078M] #check (Ring.DirectLimit.comap_surjective :
  ∀ (A : ι → Type v) [∀ i, CommRing (A i)]
    (f : ∀ i j, i ≤ j → A i →+* A j) [DirectedSystem A (f · · ·)],
    (∀ ⦃i j⦄ (hij : i ≤ j), Function.Surjective (PrimeSpectrum.comap (f i j hij))) →
    ∀ i : ι, Function.Surjective (PrimeSpectrum.comap (of A (f · · ·) i)))

end Ring.DirectLimit
