module

import ReasLib.CategoryTheory.DerivedCategory.SmallHom
import StacksCheckRecall

@[expose] public section

/- Remark 13.11.4 (`09PA`): smallness of derived-localization Hom types is owned by the neutral
K-injective API.  The first theorem is the computation core; the latter two are its explicit
quasi-isomorphism transport and replacement corollaries. -/
@[stacks 09PA] #check
  @CategoryTheory.DerivedCategory.LocalizedHom.of_kInjective
@[stacks 09PA] #check
  @CategoryTheory.DerivedCategory.LocalizedHom.of_quasiIso
@[stacks 09PA] #check
  @CategoryTheory.DerivedCategory.LocalizedHom.of_replacement
