/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.Spectral.ConstructibleTopology
import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u

namespace Ideal

/-- Let `A` be a local domain that is not a field and let `S` be a product-closed family
of finitely generated ideals. If their zero loci cover exactly the complement of the generic
point of `PrimeSpectrum A`, then the intersection of the ideals in `S` is zero. -/
theorem sInf_eq_bot_of_zeroLocus_cover {A : Type u} [CommRing A] [IsDomain A]
    [IsLocalRing A] (hA : ¬ IsField A) (S : Set (Ideal A))
    (hS_fg : ∀ I ∈ S, I.FG)
    (hS_mul : ∀ I ∈ S, ∀ J ∈ S, I * J ∈ S)
    (hS_cover :
      (⋃ I ∈ S, PrimeSpectrum.zeroLocus (I : Set A)) =
        ({(⊥ : PrimeSpectrum A)} : Set (PrimeSpectrum A))ᶜ) :
    sInf S = ⊥ := sorry

/-- If `A` is a local ring, `I` is a proper ideal, `J` is finitely generated, and
`I ≤ J ^ n` for every positive `n`, then the zero locus of `I` contains the ambient
images of the closed points of the complement of the zero locus of `J`. -/
theorem zeroLocus_contains_closedPoints_compl {A : Type u} [CommRing A] [IsLocalRing A]
    (I J : Ideal A) (hI : I ≠ ⊤) (hJ : J.FG)
    (hIJ : ∀ n : ℕ, 1 ≤ n → I ≤ J ^ n) :
    Subtype.val '' closedPoints
      ((PrimeSpectrum.zeroLocus (J : Set A))ᶜ : Set (PrimeSpectrum A)) ⊆
      PrimeSpectrum.zeroLocus (I : Set A) := sorry

end Ideal
