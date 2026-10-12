/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Order.WithBotTop
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sets.Closeds
public import ReasLib.RingTheory.Completion.LocalRing
public import ReasLib.RingTheory.Ideal.Quotient.PrimeSpectrum
public import stacks_project.Chap51.Lemma_51_4_5_CohomologicalDimension
import StacksCheckRecall

@[expose] public section

noncomputable section

universe u

namespace Ideal.LocalCohomology

variable {A : Type u} [CommRing A] [IsNoetherianRing A] [IsCompleteLocalRing A]

/-- Lemma 52.14.1 (1): for a Noetherian complete local ring `A`, a proper ideal
`I`, and a closed `Z ⊆ V(I)`, the complement `V(I) \ Z` is connected when its
dimension satisfies the additive encoding `dim Z + cd(A, I) + 1 < min (c + 1) d`,
where `c` and `d` are the source minimum dimensions. -/
@[stacks 0ECR]
theorem zeroLocus_diff_connected_of_dimension_lt
    (I : Ideal A) (hI : I ≠ ⊤) (c d : EInt)
    (h_d : IsLeast
      (Set.range fun W : irreducibleComponents (PrimeSpectrum A) ↦
        WithBot.map (WithTop.map Int.ofNat)
          (topologicalKrullDim (W : Set (PrimeSpectrum A)))) d)
    (h_c : IsLeast
      (Set.image
        (fun W : TopologicalSpace.Closeds (PrimeSpectrum A) ↦
          WithBot.map (WithTop.map Int.ofNat)
            (topologicalKrullDim (W : Set (PrimeSpectrum A))))
        {W : TopologicalSpace.Closeds (PrimeSpectrum A) |
          ¬ _root_.IsConnected (Set.univ \ (W : Set (PrimeSpectrum A)))}) c)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum A))
    (hZI : (Z : Set (PrimeSpectrum A)) ⊆ PrimeSpectrum.zeroLocus (I : Set A))
    (h_dim :
      WithBot.map (WithTop.map Int.ofNat)
          (topologicalKrullDim (Z : Set (PrimeSpectrum A))) +
        (dimension I I.fg_of_isNoetherianRing : EInt) + (1 : EInt) <
          min (c + (1 : EInt)) d) :
    _root_.IsConnected
      (PrimeSpectrum.zeroLocus (I : Set A) \ (Z : Set (PrimeSpectrum A))) := sorry

/-- Lemma 52.14.1 (2): under the same hypotheses, if the local-cohomological
dimension satisfies the additive encoding `cd(A, I) + 1 < min (c + 1) d`, then
the nonmaximal-prime locus of `A ⧸ I` is connected. -/
@[stacks 0ECR]
theorem quotient_nonmaximalPrimes_connected
    (I : Ideal A) (hI : I ≠ ⊤) (c d : EInt)
    (h_d : IsLeast
      (Set.range fun W : irreducibleComponents (PrimeSpectrum A) ↦
        WithBot.map (WithTop.map Int.ofNat)
          (topologicalKrullDim (W : Set (PrimeSpectrum A)))) d)
    (h_c : IsLeast
      (Set.image
        (fun W : TopologicalSpace.Closeds (PrimeSpectrum A) ↦
          WithBot.map (WithTop.map Int.ofNat)
            (topologicalKrullDim (W : Set (PrimeSpectrum A))))
        {W : TopologicalSpace.Closeds (PrimeSpectrum A) |
          ¬ _root_.IsConnected (Set.univ \ (W : Set (PrimeSpectrum A)))}) c)
    (h_dim :
      (dimension I I.fg_of_isNoetherianRing : EInt) + (1 : EInt) <
        min (c + (1 : EInt)) d) :
    _root_.IsConnected {p : PrimeSpectrum (A ⧸ I) | ¬ p.asIdeal.IsMaximal} := sorry

end Ideal.LocalCohomology
