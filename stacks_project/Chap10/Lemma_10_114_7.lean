/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.RingTheory.CohenMacaulay.DimensionStrata
import StacksCheckRecall

@[expose] public section

/-!
# Cohen-Macaulay Dimension Strata

@stack 00OV
-/

/- Lemma 10.114.7 (1) (Stacks tag `00OV`): the nonempty local-dimension
strata of a finite-type Cohen-Macaulay algebra over a field form a finite
clopen cover of its prime spectrum. -/
@[stacks 00OV "(1), finite clopen dimension-stratum cover"]
#check @Algebra.CohenMacaulay.existsFiniteClopenDimensionStrataCover

/- Lemma 10.114.7 (3) (Stacks tag `00OV`): every nonempty dimension-`d`
stratum of a finite-type Cohen-Macaulay algebra over a field is
equidimensional of dimension `d`. -/
@[stacks 00OV "(3), equidimensional dimension strata"]
#check @Algebra.CohenMacaulay.dimensionStratum_equidimensional_and_dimension_eq

@[stacks 00OV "(2), disjoint dimension strata"]
#check @PrimeSpectrum.pairwiseDisjoint_dimensionStratum

/- Lemma 10.114.7 (4) (Stacks tag `00OV`): equivalently, the algebra is a
finite product of its nonempty dimension-stratum factors, and every maximal
ideal of the factor indexed by `d` has height `d`. -/
@[stacks 00OV "(4), product decomposition by dimension strata"]
#check @Algebra.CohenMacaulay.existsDimensionStrataProduct
