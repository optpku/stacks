/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.RingHom.Spectrum.DenseRange
import StacksCheckRecall

/-!
# Dense spectrum maps and minimal points

@stack 00FL
-/

@[expose] public section

/- Lemma 10.30.6 (Tag 00FL): the source's kernel, minimal-point, and dense-range conditions are
the reusable `PrimeSpectrum.denseRange_comap_tfae` for an arbitrary ring homomorphism. -/
@[stacks 00FL]
#check @PrimeSpectrum.denseRange_comap_tfae

/- The point-language bridge is new; the kernel and minimal-prime views remain canonical Mathlib
owners and are checked directly in the shared leaf. -/
@[stacks 00FL "dense range and minimal points"]
#check @PrimeSpectrum.denseRange_comap_iff_minimalPoints

@[stacks 00FL "dense range and kernel"]
#check @PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical
