module

public import ReasLib.AlgebraicGeometry.Scheme.AffineAlgebraization.AssociatedPoints
public import ReasLib.RingTheory.Ideal.Localization
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

universe u

namespace PrimeSpectrum

/-- For nested ideals `I ≤ a` of a Noetherian commutative ring that is `I`-adically
complete and admits a canonical dualizing complex, `V(I) ∖ V(a)` is empty or connected
if every nonempty open neighborhood is connected and the dimension of `(A/p)_q` is
strictly greater than `cd(A, I) + 1` for every minimal prime `p` outside `V(I)` and
every prime `q` in `V(p) ∩ V(a)`. -/
@[stacks 0EG5]
theorem zeroLocus_diff_empty_or_connected_of_isAdicComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I a : Ideal A) (hIa : I ≤ a)
    (h_dualizing : CategoryTheory.DerivedCategory.HasCanonicalDualizingComplex A)
    [IsAdicComplete I A]
    (h_dimension : ∀ p q : PrimeSpectrum A,
      p.asIdeal ∈ minimalPrimes A →
        p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
          q ∈ PrimeSpectrum.zeroLocus (p.asIdeal : Set A) ∩
            PrimeSpectrum.zeroLocus (a : Set A) →
              ((Ideal.LocalCohomology.dimension I
                  I.fg_of_isNoetherianRing + 1 : ℤ) : EInt) <
                WithBot.map (WithTop.map Int.ofNat)
                  (ringKrullDim (p.asIdeal.quotientAtPrime q)))
    (h_connectedNeighborhoods : ∀ V : Set (PrimeSpectrum A),
      IsOpen V → V.Nonempty →
        PrimeSpectrum.zeroLocus (I : Set A) \
            PrimeSpectrum.zeroLocus (a : Set A) ⊆ V →
          _root_.IsConnected V) :
    PrimeSpectrum.zeroLocus (I : Set A) \
          PrimeSpectrum.zeroLocus (a : Set A) = ∅ ∨
      _root_.IsConnected
        (PrimeSpectrum.zeroLocus (I : Set A) \
          PrimeSpectrum.zeroLocus (a : Set A)) := sorry

end PrimeSpectrum
