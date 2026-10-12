/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import StacksCheckRecall
public import ReasLib.RingTheory.CohenMacaulay.Fiber.Locus

@[expose] public section

/-!
# Cohen--Macaulay fiber dimension-stratum recall

The shared owner keeps the fiber Cohen--Macaulay locus and its
exact-relative-dimension refinement independent of topology.  The source
openness assertion is the corresponding finite-presentation flatness lemma.

@stack 00RH
-/

/- Lemma 10.130.4, tag 00RH: for a flat finitely presented algebra `R → S`, the locus of
`q : Spec(S)` where the local residue-field fiber is Cohen--Macaulay with relative dimension
exactly `d` is open. -/
@[stacks 00RH "openness of a Cohen-Macaulay fiber dimension stratum"]
#check @PrimeSpectrum.CohenMacaulayFiberDimensionStratum.isOpen_of_finitePresentation_flat
