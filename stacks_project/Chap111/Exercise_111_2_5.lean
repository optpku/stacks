/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Colimit.Ring
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u v

namespace Ring.DirectLimit

variable {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
variable (A : ι → Type v) [∀ i, CommRing (A i)]
variable (f : ∀ i j, i ≤ j → A i →+* A j) [DirectedSystem A (f · · ·)]

/-- Exercise 111.2.5: if `ι` is a directed set and `(A, f)` is a directed system of
commutative rings with colimit `Ring.DirectLimit A (f · · ·)`, and if
`PrimeSpectrum.comap (f i j hij)` is surjective for all `i ≤ j`, then
`PrimeSpectrum.comap (of A (f · · ·) i)` is surjective for every stage `i`. -/
@[stacks 078M]
theorem comap_surjective
    (hf : ∀ ⦃i j⦄ (hij : i ≤ j), Function.Surjective (PrimeSpectrum.comap (f i j hij)))
    (i : ι) : Function.Surjective (PrimeSpectrum.comap (of A (f · · ·) i)) :=
  sorry

/-- If `PrimeSpectrum.comap (of A (f · · ·) i)` is surjective, then each preceding
transition `PrimeSpectrum.comap (f i j hij)` is surjective. -/
theorem comap_transition_surjective {i j : ι} (hij : i ≤ j)
    (h : Function.Surjective (PrimeSpectrum.comap (of A (f · · ·) i))) :
    Function.Surjective (PrimeSpectrum.comap (f i j hij)) :=
  sorry

end Ring.DirectLimit
