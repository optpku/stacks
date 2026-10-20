module

import ReasLib.Algebra.Homology.CochainComplex.Truncation.LowerResolution.Injective.Derived
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.34.6

The lower-truncation injective-resolution API owns the canonical map to the
inverse limit, its derived-limit comparison data, and the exact
quasi-isomorphism/isomorphism criterion.  This recall keeps the source label
while avoiding a second Chapter 13 implementation of the same Milnor-limit
argument.
-/

/- Lemma 13.34.6 (Stacks 070M) (1): an injective lower-truncation resolution
tower has an inverse limit in cochain complexes. -/
@[stacks 070M] #check
  @CochainComplex.LowerTruncation.Resolution.hasLimit

/- Lemma 13.34.6 (Stacks 070M) (2): that inverse-limit complex is
K-injective. -/
@[stacks 070M] #check
  @CochainComplex.LowerTruncation.Resolution.limit_isKInjective

/- Lemma 13.34.6 (Stacks 070M) (3): the inverse-limit complex represents the
derived limit of the canonical lower-truncation tower. -/
@[stacks 070M] #check
  @CochainComplex.LowerTruncation.Resolution.Comparison.limit

/- Lemma 13.34.6 (Stacks 070M) (4): the canonical map into that inverse limit
is the compatible comparison to the derived lower-truncation limit. -/
@[stacks 070M] #check
  @CochainComplex.LowerTruncation.Resolution.Comparison.intoLimit

/- Lemma 13.34.6 (Stacks 070M) (5): the canonical map is a quasi-isomorphism
exactly when any compatible derived comparison is an isomorphism. -/
@[stacks 070M] #check
  @CochainComplex.LowerTruncation.Resolution.Comparison.quasiIso_iff
