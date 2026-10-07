module

public import StacksCheckRecall.CommandCrossRef
public import ReasLib.CategoryTheory.Sites.Cofiltered.ColimitSection

/-!
# Auxiliary quotient sections

The reusable quotient construction formerly implemented in this supporting
chapter file is owned by
`CategoryTheory.CofilteredSiteDiagram.ColimitSection`.  It presents sections
of a colimit-site sheaf by stage representatives, common lowering, and a
quotient; downstream files should import that ReasLib leaf directly.
-/

@[expose] public section

namespace CategoryTheory.CofilteredSiteDiagram

/- Lemma 7.18.3 (0A35): the auxiliary quotient construction used in the
filtered-colimit argument is available as a reusable colimit-site section
API. -/
@[stacks 0A35 "auxiliary quotient sections"] #check @ColimitSection.Representative

#check @ColimitSection.Representative.lower
#check @ColimitSection.Section
#check @ColimitSection.Section.mk
#check @ColimitSection.RestrictionData
#check @ColimitSection.restrict
#check @ColimitSection.presheaf
#check @ColimitSection.sheaf
#check @ColimitSection.stageMap
#check @ColimitSection.stageMap_app
#check @ColimitSection.unit

end CategoryTheory.CofilteredSiteDiagram
