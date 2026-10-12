/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

import ReasLib.Algebra.Homology.CochainComplex.Filtration.FilteredInjective.Resolution
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 13.26.7

The compatible lifting of morphisms between filtered quasi-isomorphisms to bounded-below
filtered-injective complexes is owned by the same ReasLib resolution API as Lemma 13.26.6.
-/

namespace CochainComplex.FilteredInjectivePlus

/- Lemma 13.26.7 (`05TU`): a morphism of finite filtered objects lifts to a morphism between a
strict filtered-injective replacement of its source and a prescribed filtered-injective target
replacement. -/
@[stacks 05TU] #check
  @exists_map_of_quasiIsos

end CochainComplex.FilteredInjectivePlus
