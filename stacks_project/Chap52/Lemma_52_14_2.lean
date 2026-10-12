/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap52.Proposition_52_12_3
public import ReasLib.RingTheory.Ideal.Localization
public import Mathlib.Topology.Connected.Basic
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

namespace AlgebraicGeometry.AffineAlgebraizationSetup

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- Lemma 52.14.2: let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`. Assume that
`A` is `I`-adically complete and has a dualizing complex, that the stated strict
local-dimension bound holds at minimal primes, and that every nonempty open
neighborhood of `V(I) ∖ V(𝔞)` is connected. Then `V(I) ∖ V(𝔞)` is empty or
connected. -/
@[stacks 0EG5]
theorem zeroLocus_diff_empty_or_connected
    [MonoidalCategory (DerivedCategory (ModuleCat.{u} A))]
    (S : AffineAlgebraizationSetup A)
    (H : MonoidalClosed (DerivedCategory (ModuleCat.{u} A)))
    (h_dualizing :
      ∃ K : DerivedCategory (ModuleCat.{u} A), K.IsDualizingComplex H)
    [IsAdicComplete S.I A]
    (h_dimension : ∀ p q : PrimeSpectrum A,
      p.asIdeal ∈ minimalPrimes A →
        p ∉ PrimeSpectrum.zeroLocus (S.I : Set A) →
          q ∈ PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
            PrimeSpectrum.zeroLocus (S.a : Set A) →
              ((Ideal.LocalCohomology.dimension S.I
                  S.I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim (p.asIdeal.quotientAtPrime q)))
    (h_connectedNeighborhoods : ∀ V : Set (PrimeSpectrum A),
      IsOpen V → V.Nonempty →
        PrimeSpectrum.zeroLocus (S.I : Set A) \
            PrimeSpectrum.zeroLocus (S.a : Set A) ⊆ V →
          _root_.IsConnected V) :
    PrimeSpectrum.zeroLocus (S.I : Set A) \
          PrimeSpectrum.zeroLocus (S.a : Set A) = ∅ ∨
      _root_.IsConnected
        (PrimeSpectrum.zeroLocus (S.I : Set A) \
          PrimeSpectrum.zeroLocus (S.a : Set A)) := sorry

end AlgebraicGeometry.AffineAlgebraizationSetup
