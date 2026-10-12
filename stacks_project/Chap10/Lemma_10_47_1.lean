/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Geometrically.Affine.Descent
import StacksCheckRecall

@[expose] public section

/-!
# Irreducibility from Fibers

The reusable ring-level owners are in `PrimeSpectrum`: the open-map criterion
and its flat finite-presentation specialization.  This chapter item retains
the source label as a direct recall rather than duplicating the fiber transport.

@stack 00I6
-/

/- Lemma 10.47.1 (Tag 00I6): if `Spec R` is irreducible, `R → S` is flat and of finite
presentation, and the spectra of `κ(p) ⊗[R] S` are irreducible for a dense set of primes `p`,
then `Spec S` is irreducible. -/
@[stacks 00I6]
#check @PrimeSpectrum.irreducible_of_flat_finitePresentation
