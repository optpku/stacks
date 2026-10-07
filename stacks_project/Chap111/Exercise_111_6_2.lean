module

public import ReasLib.RingTheory.Spectrum.Prime.BasicOpen
import StacksCheckRecall

@[expose] public section

/- Exercise 111.6.2: for a ring `A` and `f ∈ A`, the standard open `D(f)` is
`PrimeSpectrum.basicOpen f`, whose points are the primes not containing `f`. These standard
opens form a basis of the Zariski topology on `PrimeSpectrum A`. -/
@[stacks 02CZ]
#check (PrimeSpectrum.isTopologicalBasis_notMem :
  ∀ {A : Type _} [CommRing A], TopologicalSpace.IsTopologicalBasis
    (Set.range fun f : A => {p : PrimeSpectrum A | f ∉ p.asIdeal}))

/- Companion: source definition of `D(f)` as the standard open. -/
#check @PrimeSpectrum.basicOpen

/- Companion: membership formula `p ∈ basicOpen f ↔ f ∉ p.asIdeal`. -/
#check @PrimeSpectrum.mem_basicOpen

/- Companion: bundled `Opens.IsBasis` packaging of the same basis. -/
#check @PrimeSpectrum.isBasis_basic_opens
