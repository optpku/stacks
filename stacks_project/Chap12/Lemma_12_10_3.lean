module

public import ReasLib.CategoryTheory.ObjectProperty.WeakSerre
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.ObjectProperty

/- Lemma 12.10.3 [0754]: weak Serre classes inherit the canonical closure and abelian
subcategory instances. -/
#check ObjectProperty.IsWeakSerreClass.closedUnderIsomorphisms
#check ObjectProperty.IsWeakSerreClass.closedUnderBinaryProducts
#check ObjectProperty.IsWeakSerreClass.closedUnderFiniteProducts

/- Lemma 12.10.3 [0754]: the inclusion of the associated full subcategory is exact. -/
@[stacks 0754]
#check ObjectProperty.IsWeakSerreClass.Inclusion.isExact

/- Exactness exposes the standard preservation interfaces directly to downstream consumers. -/
#check ObjectProperty.IsWeakSerreClass.Inclusion.preservesFiniteLimits
#check ObjectProperty.IsWeakSerreClass.Inclusion.preservesFiniteColimits
