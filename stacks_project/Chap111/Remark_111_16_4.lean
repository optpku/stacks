module

public import ReasLib.RingTheory.Spectrum.Prime.Jacobson.Polynomial
import StacksCheckRecall

@[expose] public section

universe u

variable {k : Type u} [Field k] {n : ℕ}

/- Remark 111.16.4: this is the Hilbert Nullstellensatz. Closed subsets of
`PrimeSpectrum (MvPolynomial (Fin n) k)` (which correspond to radical ideals by
`PrimeSpectrum.isClosed_iff_zeroLocus_radical_ideal`) are determined by the closed
points they contain: every closed set equals the closure of its intersection with
`closedPoints`. -/
@[stacks 02DQ] #check (PrimeSpectrum.closure_inter_closedPoints_mvPolynomial :
    ∀ {Z : Set (PrimeSpectrum (MvPolynomial (Fin n) k))}, IsClosed Z →
      closure (Z ∩ closedPoints (PrimeSpectrum (MvPolynomial (Fin n) k))) = Z)
