/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.DerivedCategory.ModulesOnCategory.QuasiCoherent.Map
import StacksCheckRecall

@[expose] public section

open CategoryTheory

namespace CategoryTheory.ModulesOnCategory.QuasiCoherent

/- Lemma 24.33.4: a derived pullback maps a quasi-coherent object to a quasi-coherent object once
the sectionwise base-change comparison transports every source comparison isomorphism to the
corresponding target comparison isomorphism. -/
@[stacks 0GZC] #check @map_mem

/- Lemma 24.33.4, property-level form: the source comparison locus is contained in the inverse
image of the target comparison locus. -/
@[stacks 0GZC "property-level form"] #check @le_inverseImage

/- The induced functor on quasi-coherent full subcategories is the canonical restriction of the
ambient derived pullback. -/
#check @ObjectProperty.FullSubcategory.restrict

end CategoryTheory.ModulesOnCategory.QuasiCoherent
