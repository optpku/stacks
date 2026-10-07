module

public import stacks_project.Chap90.Lemma_90_19_7_Comparison
public import stacks_project.Chap90.Lemma_90_19_7_TangentSpace
import StacksCheckRecall

/-!
# Lemma 90.19.7

If `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids and satisfies (RS),
then for `x : F` the identity-tangent space `T_id Aut(x)` carries a natural
`k`-vector space structure whose addition agrees with composition, and there is a
canonical `k`-linear isomorphism with `T_id Aut(x0)` for `x0` the selected
residue-field pushforward of `x`.
-/

@[expose] public section

open CategoryTheory hiding Linear
open CategoryTheory.Functor
open ArtinianLocalAlgCat

/- Lemma 90.19.7 (1): Let `F` be a category cofibered in groupoids over `C_Λ`
satisfying (RS). Let `x` be an object of `F(A)`. Then `T_id Aut(x)` has a natural
`k`-vector space structure such that addition agrees with composition in
`T_id Aut(x)`. In particular, composition in `T_id Aut(x)` is commutative. -/
@[stacks 06JV]
#check idTangentSpace_add_eq_mul

/- Lemma 90.19.7 (2): There is a canonical isomorphism
`T_id Aut(x) ≃ₗ[k] T_id Aut(x0)` of `k`-vector spaces, where `x0` is the selected
pushforward of `x` to `F(k)`. -/
@[stacks 06JV]
#check idTangentSpaceLinearEquiv
