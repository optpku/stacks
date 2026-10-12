/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap63.Remark_63_3_5_Covariance_with_respect_to_open_embeddings_OpenImmersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

/- Remark 63.3.5 (Covariance with respect to open embeddings) (1): if
`f : X ⟶ Y` is separated and locally of finite type, `F` is an abelian sheaf
on `X_étale`, and `j : X' ⟶ X` is an open immersion, there is a canonical
map `etaleLowerShriekOpenImmersion j f : f'_!(F|_{X'}) ⟶ f_! F`. -/
@[stacks 0F53]
#check etaleLowerShriekOpenImmersion

/- Remark 63.3.5 (Covariance with respect to open embeddings) (2): the
canonical comparison `f'_!(F|_{X'}) ⟶ f_! F` is injective. -/
@[stacks 0F53]
#check etaleLowerShriekOpenImmersion_app_mono

/- Remark 63.3.5 (Covariance with respect to open embeddings) (3): the
comparison fills the triangle with the compact-support inclusions
`etaleLowerShriekι` and the restriction of ordinary pushforwards
`etaleAbelianPushforwardRestrict`. -/
@[stacks 0F53]
#check etaleLowerShriekOpenImmersion_ι

/- Remark 63.3.5 (Covariance with respect to open embeddings) (4): for nested
open immersions `X'' ⟶ X' ⟶ X`, the composite of the two covariance maps is
the covariance map of the composite open immersion. -/
@[stacks 0F53]
#check etaleLowerShriekOpenImmersion_comp

end
