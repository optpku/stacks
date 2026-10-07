module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Support
import StacksCheckRecall

@[expose] public section

/- Lemma 17.5.2 (1): the support of a local module section is closed in its domain. -/
@[stacks 01AU "(1)"]
#check @SheafOfModules.isClosed_localSectionSupport

/- Lemma 17.5.2 (2): the support of a scalar multiple lies in the intersection of the supports of
the scalar and the section. -/
@[stacks 01AU "(2)"]
#check @SheafOfModules.localSectionSupport_smul_subset

/- Lemma 17.5.2 (3): the support of a sum lies in the union of the two section supports. -/
@[stacks 01AU "(3)"]
#check @SheafOfModules.localSectionSupport_add_subset

/- Lemma 17.5.2 (4): a module sheaf's support is the union of the ambient images of all local
section supports. -/
@[stacks 01AU "(4)"]
#check @SheafOfModules.support_eq_iUnion_localSectionSupport

/- Lemma 17.5.2 (5): a morphism of module sheaves cannot enlarge a local section's support. -/
@[stacks 01AU "(5)"]
#check @SheafOfModules.localSectionSupport_map_subset
