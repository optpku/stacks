/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.CohenMacaulay.Locus
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 10.130.3: density of the Cohen--Macaulay locus

@stack 00RG

The reusable locus and minimal-prime API is owned by
`ReasLib.RingTheory.CohenMacaulay.Locus`.  In the finite-type situation the
source's dense-open conclusion is recalled through its dense owner and the
preceding open-locus owner.
-/

universe u v

variable {k : Type u} [Field k]
variable {S : Type v} [CommRing S] [Algebra k S] [Algebra.FiniteType k S]

/- Lemma 10.130.3 (Stacks `00RG`): the Cohen--Macaulay locus is dense. -/
@[stacks 00RG "dense Cohen--Macaulay locus"]
#check @PrimeSpectrum.dense_cohenMacaulayLocus S inferInstance
  (Algebra.FiniteType.isNoetherianRing k S)

/- Lemma 10.130.3 uses the open-locus result from Lemma 10.130.2 (Stacks `00RF`). -/
@[stacks 00RF "open Cohen--Macaulay locus"]
#check (PrimeSpectrum.isOpen_cohenMacaulayLocus_of_finiteType (k := k) (S := S))
