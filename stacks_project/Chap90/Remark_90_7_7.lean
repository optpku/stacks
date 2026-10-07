module

public import stacks_project.Chap90.Remark_90_7_7_Can
public import stacks_project.Chap90.Remark_90_7_7_Nilpotency
import StacksCheckRecall

@[expose] public section

open FormalObject

/- Remark 90.7.7 (1): if `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids,
there is a canonical evaluation functor
`can : hat F |_{C_Λ} ⟶ F` sending a formal object `(A, ξ_n, f_n)` over an Artinian
algebra `A` to the nilpotency-stage object `ξ_m`, transported along
`A ⧸ m_A^{m} ≅ A`. This is owned by `FormalObject.can`. -/
@[stacks 06SJ] #check FormalObject.can

/- Remark 90.7.7 (2): `can` is an equivalence of categories cofibered in groupoids over
`C_Λ`, because it is a fibrewise equivalence by Lemma 90.7.4 and the fact that the
`m_A`-adic topology on a local Artinian ring comes from the zero ideal. This is owned
by `FormalObject.basedCan_isEquivalence`. -/
@[stacks 06SJ] #check FormalObject.basedCan_isEquivalence

/- Remark 90.7.7 (3): one identifies `F` with a full subcategory of `hat F` via a
quasi-inverse to `can`. This is owned by `FormalObject.embed`. -/
@[stacks 06SJ] #check FormalObject.embed
