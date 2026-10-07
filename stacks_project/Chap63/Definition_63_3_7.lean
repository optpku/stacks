module

public import stacks_project.Chap63.Definition_63_3_7_CompactSupport
import StacksCheckRecall

@[expose] public section

/- Definition 63.3.7: for a separated scheme `X` locally of finite type over a
field `k` and an abelian sheaf `F` on `X_étale`, `H^0_c(X, F) ⊂ H^0(X, F)` is
the set of global étale sections whose support is proper over `k`. Elements of
this set are called sections with compact support. -/
@[stacks 0F72] #check AlgebraicGeometry.Scheme.Etale.globalSectionsCompactSupport

end
