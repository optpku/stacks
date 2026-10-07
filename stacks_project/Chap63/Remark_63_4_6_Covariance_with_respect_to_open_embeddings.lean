module

public import stacks_project.Chap63.Remark_63_4_6_Covariance_with_respect_to_open_embeddings_Comparison
public import stacks_project.Chap63.Remark_63_4_6_Covariance_with_respect_to_open_embeddings_OpenImmersion
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale

/- Remark 63.4.6 (Covariance with respect to open embeddings) (1): if
`f : X ⟶ Y` is locally quasi-finite, `F` is an abelian sheaf on `X_étale`,
and `j : X' ⟶ X` is an open immersion, there is a canonical map
`lowerShriekOpenImmersion j f : f'_!(F|_{X'}) ⟶ f_! F`. -/
@[stacks 0F6S]
#check lowerShriekOpenImmersion

/- Remark 63.4.6 (Covariance with respect to open embeddings) (2): the maps
`f'_{p!}(F|_{X'}) ⟶ f_{p!} F` and `f'_!(F|_{X'}) ⟶ f_! F` are compatible with
the stalk descriptions of Lemmas 63.4.2 and 63.4.5. -/
@[stacks 0F6S]
#check lowerShriekOpenImmersion_stalk

/- Remark 63.4.6 (Covariance with respect to open embeddings) (3): if `f` is
separated, the presheaf covariance `f'_{p!}(F|_{X'}) ⟶ f_{p!} F` agrees with
the map of Remark 63.3.5 via the isomorphism of Lemma 63.4.1. -/
@[stacks 0F6S]
#check lowerShriekPresheafOpenImmersion_separated

/- Remark 63.4.6 (Covariance with respect to open embeddings) (4): for nested
open immersions `X'' ⟶ X' ⟶ X`, the composite of the two covariance maps is
the covariance map of the composite open immersion. -/
@[stacks 0F6S]
#check lowerShriekOpenImmersion_comp

/- Remark 63.4.6 (Covariance with respect to open embeddings) (5): the
canonical comparison `f'_!(F|_{X'}) ⟶ f_! F` is injective. -/
@[stacks 0F6S]
#check lowerShriekOpenImmersion_app_mono

end
