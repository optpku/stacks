module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Pushforward.Exact
import StacksCheckRecall

/-!
# Lemma 61.25.6

Exactness of the small pro-étale abelian direct image along a closed immersion
of schemes whose complement is a retrocompact open.
-/

public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/- Lemma 61.25.6: if `i : Z ⟶ X` is a closed immersion of schemes and
`(Set.range i)ᶜ` is a retrocompact open of `X`, then
`smallPushforward i` is an exact functor
`Sheaf (topology Z) AddCommGrpCat ⥤ Sheaf (topology X) AddCommGrpCat`. -/
@[stacks 09BM] #check
  (AlgebraicGeometry.Scheme.ProEt.smallPushforward_exact_of_isRetrocompact_compl :
    ∀ {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i],
    IsRetrocompact (Set.range i)ᶜ →
    exactFunctor (Sheaf (topology Z) AddCommGrpCat.{u + 1})
      (Sheaf (topology X) AddCommGrpCat.{u + 1}) (smallPushforward i))

end AlgebraicGeometry.Scheme.ProEt
