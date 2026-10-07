module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import ReasLib.Topology.KrullDimension.Equidimensional
public import ReasLib.RingTheory.CohenMacaulay.Ring
public import ReasLib.RingTheory.RingHom.Fiber.Local
public import ReasLib.RingTheory.KrullDimension.Fiber
import StacksCheckRecall

@[expose] public section

/-! @stack 00RA

The regular-sequence locus is kept as a concrete subset of the canonical zero-locus subtype
`PrimeSpectrum.zeroLocus (Ideal.ofList fs : Set S)`.  The membership theorem is the direct
pointwise bridge, and the labeled result records its openness under the fiberwise hypotheses.
-/

universe u v

open PrimeSpectrum
open scoped PrimeSpectrum TensorProduct

section

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

/-- The source-facing locus inside `V(Ideal.ofList fs)` where the images of `fs` form a regular
sequence in the corresponding local fiber ring. -/
def fiberLocalRingRegularSequenceLocus (R : Type u) [CommRing R]
    (S : Type v) [CommRing S] [Algebra R S] (fs : List S) :
    Set (PrimeSpectrum.zeroLocus (Ideal.ofList fs : Set S)) :=
  { q | q.1.IsRegularInFiberLocalRing R fs }

/-- Membership in `fiberLocalRingRegularSequenceLocus` is the fiber-local regular-sequence
condition at the corresponding point. -/
theorem mem_fiberLocalRingRegularSequenceLocus_iff
    (fs : List S) (q : PrimeSpectrum.zeroLocus (Ideal.ofList fs : Set S)) :
    q ∈ fiberLocalRingRegularSequenceLocus R S fs ↔
      q.1.IsRegularInFiberLocalRing R fs := sorry

/-- Lemma 10.129.2: for a finite type map `R → S` whose fibers are Cohen--Macaulay,
equidimensional, and of fixed dimension `d`, the points of `V(Ideal.ofList fs)` where `fs` is
regular in the fiber local ring form an open subset of that zero locus. -/
@[stacks 00RA]
theorem isOpen_fiberLocalRingRegularSequenceLocusWithinZeroLocus_of_fiberwise_cohenMacaulay_equidimensional
    [Algebra.FiniteType R S] (d : ℕ) (fs : List S)
    (hCM : ∀ p : PrimeSpectrum R, CohenMacaulayRing (p.asIdeal.Fiber S))
    (hEqdim : ∀ p : PrimeSpectrum R,
      TopologicalSpace.EquidimensionalSpace (PrimeSpectrum (p.asIdeal.Fiber S)))
    (hDim : ∀ p : PrimeSpectrum R, ringKrullDim (p.asIdeal.Fiber S) = d) :
    IsOpen (fiberLocalRingRegularSequenceLocus R S fs) := sorry

end
