module

import ReasLib.Algebra.Homology.HomotopyCategory.KInjective.Local
import ReasLib.Algebra.Homology.DerivedCategory.KInjective.Localization
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.31.2

The textbook three-way criterion is represented by two composable
K-injectivity characterizations: homotopy-locality at quasi-isomorphisms and
bijectivity of the homotopy-to-derived comparison map.
-/

/- Lemma 13.31.2 (Stacks 070I) (1): K-injectivity is equivalent to
homotopy-locality at quasi-isomorphisms. -/
@[stacks 070I] #check
  @CochainComplex.IsKInjective.iff_precomp_bijective_of_quasiIso

/- Lemma 13.31.2 (Stacks 070I) (2): K-injectivity is equivalent to
bijectivity of the homotopy-to-derived comparison map. -/
@[stacks 070I] #check @CochainComplex.IsKInjective.iff_Qh_map_bijective

/- The localization-neutral computation API does not choose a derived-category model. -/
@[stacks 070I] #check @CochainComplex.IsKInjective.map_bijective
@[stacks 070I] #check @CochainComplex.IsKInjective.homEquiv
@[stacks 070I] #check @CochainComplex.IsKInjective.fullyFaithfulTo
