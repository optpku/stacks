module

public import stacks_project.Chap63.Lemma_63_3_1_ProperSupport
import StacksCheckRecall

@[expose] public section

/- Lemma 63.3.1: if `f : X ⟶ Y` is locally of finite type and `F` is an abelian sheaf
on `X_étale`, the rule sending `V` in `Y_étale` to the subgroup of
`(etaleDirectImage f).obj F` on `V`, identified with `F(X_V)`, consisting of
sections whose étale support in `X_V` is proper over `V`, is an abelian subsheaf
of `f_* F`. -/
@[stacks 0F4X] #check AlgebraicGeometry.Scheme.Etale.isSheaf_properSupportSubfunctor

end
