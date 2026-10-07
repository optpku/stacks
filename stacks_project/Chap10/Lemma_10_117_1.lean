module

public import ReasLib.RingTheory.GradedAlgebra.Irrelevant.Hilbert
import StacksCheckRecall

@[expose] public section

/-!
# The Irrelevant Point of a Standard Graded Algebra

Lemma 10.117.1, tag `00P6`, is maintained by the reusable irrelevant-ideal,
local-dimension, and Hilbert--Samuel APIs in `ReasLib`.

@stack 00P6
-/

/- Lemma 10.117.1 (1): the irrelevant ideal is maximal when the degree-zero
piece is identified with the base field. -/
@[stacks 00P6 "(1)"]
#check @HomogeneousIdeal.irrelevant_isMaximal_of_degreeZeroEquiv

/- Lemma 10.117.1 (2): minimal primes are homogeneous and lie below the
irrelevant ideal. -/
@[stacks 00P6 "(2), homogeneity"]
#check @Ideal.isHomogeneous_of_mem_minimalPrimes

@[stacks 00P6 "(2), containment"]
#check @HomogeneousIdeal.minimalPrime_le_irrelevant_of_degreeZeroEquiv

/- Lemma 10.117.1 (3): the global dimension is both one more than the degree
of the graded Hilbert polynomial and the local topological dimension at the
irrelevant point. -/
@[stacks 00P6 "(3), Hilbert polynomial"]
#check @HomogeneousIdeal.Irrelevant.ringKrullDim_eq_degree_succ_of_eventuallyEq_finrank

@[stacks 00P6 "(3), local topological dimension"]
#check @HomogeneousIdeal.Irrelevant.ringKrullDim_eq_topologicalKrullDimAt

/- The same dimension is the Krull dimension of the irrelevant local ring. -/
#check @HomogeneousIdeal.Irrelevant.ringKrullDim_eq_localRing

/- Lemma 10.117.1 (4): the Hilbert--Samuel function of the irrelevant local
ring agrees with the finite-dimensional graded Hilbert function. -/
@[stacks 00P6 "(4)"]
#check @HomogeneousIdeal.Irrelevant.hilbertSamuelPhi_eq_finrank_of_finiteType

/- The reusable comparison is valid first at the cardinal-rank level. -/
#check @HomogeneousIdeal.Irrelevant.hilbertSamuelPhi_eq_rank
