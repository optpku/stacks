/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap63.Remark_63_3_9_Open_embeddings_and_compactly_supported_sections_OpenImmersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

/- Remark 63.3.9 (Open embeddings and compactly supported sections) (1): if
`X` is a separated scheme locally of finite type over a field `k`, `F` is an
abelian sheaf on `X_étale`, and `j : X' ⟶ X` is an open immersion over `k`,
there is a canonical map
`globalSectionsCompactSupportOpenImmersion j F : H^0_c(X', F|_{X'}) →+ H^0_c(X, F)`. -/
@[stacks 0F74]
#check globalSectionsCompactSupportOpenImmersion

/- Remark 63.3.9 (Open embeddings and compactly supported sections) (2): the
canonical comparison `H^0_c(X', F|_{X'}) ⟶ H^0_c(X, F)` is injective. -/
@[stacks 0F74]
#check globalSectionsCompactSupportOpenImmersion_injective

/- Remark 63.3.9 (Open embeddings and compactly supported sections) (3): these
maps turn `H^0_c` into a covariant functor on the Zariski opens of `X`, the
quoted “cosheaf” on the Zariski site. -/
@[stacks 0F74]
#check globalSectionsCompactSupportCopresheaf

end
