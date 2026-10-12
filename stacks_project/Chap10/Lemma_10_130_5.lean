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
# Cohen--Macaulay Fiber-Locus Topology Recall

The source packages two independent consequences of flat finite presentation:
openness of the locus and density of its restriction to every residue-field
fiber.  The shared API keeps those consequences atomic.

@stack 00RI
-/

/- Lemma 10.130.5, tag 00RI (1): for a flat finitely presented algebra, the
Cohen--Macaulay residue-field fiber locus is open. -/
@[stacks 00RI "openness and fiberwise density of the Cohen-Macaulay fiber locus"]
#check @PrimeSpectrum.isOpen_cohenMacaulayFiberLocus_of_finitePresentation_flat

/- Lemma 10.130.5, tag 00RI (2): on every finite-type residue-field fiber, the induced
Cohen--Macaulay locus is dense. -/
@[stacks 00RI "openness and fiberwise density of the Cohen-Macaulay fiber locus"]
#check @PrimeSpectrum.dense_preimage_cohenMacaulayFiberLocus_of_fiberFiniteType
