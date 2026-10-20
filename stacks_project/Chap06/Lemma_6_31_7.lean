module

public import ReasLib.Topology.Sheaf.ExtensionByInitial
import StacksCheckRecall

@[expose] public section

/- Lemma 6.31.7 (1): extension by the initial object on presheaves along an open inclusion is left
adjoint to presheaf restriction. -/
@[stacks 00A6 "presheaf extension-restriction adjunction"]
recall TopCat.Presheaf.ExtensionByInitial.Properties.adjunction

/- Lemma 6.31.7 (2): extension by the initial object on sheaves along an open inclusion is left
adjoint to sheaf restriction. -/
@[stacks 00A6 "sheaf extension-restriction adjunction"]
recall TopCat.Sheaf.ExtensionByInitial.Properties.adjunction

/- Lemma 6.31.7 (3), inside `U`: at a point of the open subset, the stalk of the extension sheaf is
canonically isomorphic to the original stalk. -/
@[stacks 00A6 "stalk of extension inside the open subset"]
recall TopCat.Sheaf.ExtensionByInitial.Properties.stalkIso_of_mem

/- Lemma 6.31.7 (3), outside `U`: the stalk of the extension sheaf is canonically isomorphic to
the chosen initial object. -/
@[stacks 00A6 "stalk of extension outside the open subset"]
recall TopCat.Sheaf.ExtensionByInitial.Properties.stalk_isInitial_of_not_mem

/- Lemma 6.31.7 (4): the unit of the canonical adjunction between presheaf extension by the
initial object and restriction along the open inclusion is an isomorphism. -/
@[stacks 00A6 "presheaf restriction after extension"]
recall TopCat.Presheaf.ExtensionByInitial.Properties.unit_isIso

/- Lemma 6.31.7 (5): the unit of the canonical adjunction between sheaf extension by the initial
object and restriction along the open inclusion is an isomorphism. -/
@[stacks 00A6 "sheaf restriction after extension"]
recall TopCat.Sheaf.ExtensionByInitial.Properties.unit_isIso
