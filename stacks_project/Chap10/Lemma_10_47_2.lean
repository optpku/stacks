module

public import ReasLib.RingTheory.Spectrum.Prime.TensorProduct
import StacksCheckRecall

@[expose] public section

/-!
# Tensor Products and Irreducible Spectra

The ring-level owner is `PrimeSpectrum.unique_minimalPrime_tensorProduct`.  The
chapter keeps only the source-facing recall, while the irreducibility/minimal-prime
conversion is shared independently of this item.

@stack 00I7
-/

/- Lemma 10.47.2 (Tag 00I7): if `k` is separably closed and the `k`-algebras `R` and `S` each
have a unique minimal prime ideal, then `R ⊗[k] S` also has a unique minimal prime ideal. -/
@[stacks 00I7]
#check @PrimeSpectrum.unique_minimalPrime_tensorProduct
