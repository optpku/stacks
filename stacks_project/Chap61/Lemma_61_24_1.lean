module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Proetale.Pushforward.Exact
import StacksCheckRecall

/-!
# Lemma 61.24.1

Exactness of the small pro-étale abelian direct image along a finite morphism
of schemes which is locally of finite presentation.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme.ProEt

/- Lemma 61.24.1: if `f : Z ⟶ X` is a finite morphism of schemes which is locally
of finite presentation, then
`smallPushforward f : Sheaf (topology Z) AddCommGrpCat ⥤ Sheaf (topology X) AddCommGrpCat`
is an exact functor. -/
@[stacks 09A8] #check (AlgebraicGeometry.Scheme.ProEt.smallPushforward_exact :
  ∀ {Z X : Scheme.{u}} (f : Z ⟶ X) [IsFinite f] [LocallyOfFinitePresentation f],
    exactFunctor (Sheaf (topology Z) AddCommGrpCat.{u + 1})
      (Sheaf (topology X) AddCommGrpCat.{u + 1}) (smallPushforward f))

end AlgebraicGeometry.Scheme.ProEt
