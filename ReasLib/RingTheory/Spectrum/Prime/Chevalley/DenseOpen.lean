/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Chevalley
import Mathlib.Tactic.CrossRefAttribute

/-!
# Dense open subsets in constructible images

@stack 00FH
-/

@[expose] public section

universe u v

open Set Topology TopologicalSpace

namespace PrimeSpectrum

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable {E : Set (PrimeSpectrum S)} {ξ : PrimeSpectrum R}

/-- Lemma 10.30.2: a point in the constructible image of a finite-type map
has an open dense neighborhood inside its closure that remains in the image. -/
@[stacks 00FH]
theorem exists_open_dense_in_comap_image
    (f : R →+* S) (hf : f.FiniteType) (hE : IsConstructible E)
    (hξ : ξ ∈ PrimeSpectrum.comap f '' E) :
    ∃ U : Opens (closure ({ξ} : Set (PrimeSpectrum R))),
      Dense (U : Set (closure ({ξ} : Set (PrimeSpectrum R)))) ∧
        (U : Set (closure ({ξ} : Set (PrimeSpectrum R)))) ⊆
          ((Subtype.val : closure ({ξ} : Set (PrimeSpectrum R)) → PrimeSpectrum R) ⁻¹'
            (PrimeSpectrum.comap f '' E)) := sorry

end PrimeSpectrum
