module

public import ReasLib.AlgebraicGeometry.Scheme.Spec.BasicOpen.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.BasicOpen
public import ReasLib.AlgebraicGeometry.Scheme.Module.Tilde.Exact
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry

/- Lemma 26.5.4: affine structure sheaves and tilde modules are computed by
localization on global sections, principal opens, and stalks. -/
@[stacks 01HV] #check Scheme.ΓSpecIso
#check StructureSheaf.globalSectionsIso
@[stacks 01HV "basic-open sections"] #check Spec.BasicOpen.sectionsIso
@[stacks 01HV "structure-sheaf restriction on basic opens"]
#check Spec.BasicOpen.sectionsIso_restriction
@[stacks 01HV "structure-sheaf stalk"] #check StructureSheaf.stalkIso
@[stacks 01HV "global sections of a tilde module"] #check tilde.isoTop
@[stacks 01HV "tilde on a basic open"] #check tilde.basicOpenIso
@[stacks 01HV "tilde restriction on basic opens"]
#check tilde.basicOpenIso_restriction
@[stacks 01HV "naturality on basic opens"] #check tilde.basicOpenIso_naturality
@[stacks 01HV "tilde stalk"] #check tilde.stalkIso
@[stacks 01HV "stalk naturality"] #check tilde.stalkIso_naturality
@[stacks 01HV "global-sections natural isomorphism"] #check tilde.toTildeΓNatIso
@[stacks 01HV "exactness of tilde"] #check tilde.exact
