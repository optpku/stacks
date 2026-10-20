module

public import ReasLib.CategoryTheory.DerivedCategory.MappingCocone.Triangle
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import StacksCheckRecall

@[expose] public section

/-!
# Lemma 21.26.1

The source chooses a K-injective model and replaces the first term of a mapping-cocone triangle.
The reusable owner is the category-generic `DerivedCategory.MappingCocone` API; this file keeps
the Stacks entry as a recall and does not introduce an abelian-group-specific wrapper.
-/

open CategoryTheory CategoryTheory.Pretriangulated
open CategoryTheory.DerivedCategory.MappingCocone

/- Lemma 21.26.1 (0F16): if `c : IX ⟶ mappingCocone β` becomes an isomorphism after localization,
the comparison triangle is distinguished; two comparison choices give the canonical isomorphism
between their derived sources. -/
@[stacks 0F16]
#check @triangleOfComparison

@[stacks 0F16]
#check @triangleOfComparisonIso

@[stacks 0F16]
#check @triangleOfComparison_distinguished

#check @comparisonIso
#check @comparisonIso_hom_comp

end
