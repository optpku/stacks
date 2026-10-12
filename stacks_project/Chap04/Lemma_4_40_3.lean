/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.CategoryTheory.Fibered.Representable.Presentation
import StacksCheckRecall

@[expose] public section

universe u v

namespace CategoryTheory

open scoped Bicategory

variable {C : Type u} [Category.{v} C]
variable {P Q : FiberedCategoryOver.Groupoids C} {X Y : C}
variable (eP : P ≌ FiberedCategoryOver.Groupoids.slice X)
variable (eQ : Q ≌ FiberedCategoryOver.Groupoids.slice Y)
variable (f : X ⟶ Y) {F G : P ⟶ Q}
variable (hF : FiberedCategoryOver.Groupoids.InducesHom F eP.hom eQ.hom f)
variable (hG : FiberedCategoryOver.Groupoids.InducesHom G eP.hom eQ.hom f)

/- Lemma 4.40.3 (1), surjectivity: for categories fibred in groupoids represented by `X` and
`Y`, every morphism `X ⟶ Y` is recovered from a `1`-morphism. -/
@[stacks 04SF "(1) surjectivity"]
#check (FiberedCategoryOver.Groupoids.Presentation.recover.surjective eP eQ :
  Function.Surjective
    (FiberedCategoryOver.Groupoids.Presentation.recover eP eQ))

/- Lemma 4.40.3 (1), isomorphism classes: two `1`-morphisms between represented categories
fibred in groupoids determine the same map `X ⟶ Y` exactly when they are `2`-isomorphic. -/
@[stacks 04SF "(1) isomorphism classes"]
#check (FiberedCategoryOver.Groupoids.Presentation.recover.eq_iff_isomorphic eP eQ F G :
  FiberedCategoryOver.Groupoids.Presentation.recover eP eQ F =
      FiberedCategoryOver.Groupoids.Presentation.recover eP eQ G ↔
    IsIsomorphic F G)

/- Lemma 4.40.3 (2), existence: every `f : X ⟶ Y` is induced by a `1`-morphism between the
represented categories fibred in groupoids. -/
@[stacks 04SF "(2) existence"]
#check (FiberedCategoryOver.Groupoids.InducesHom.exists_morphism eP eQ f :
  ∃ H : P ⟶ Q,
    FiberedCategoryOver.Groupoids.InducesHom H eP.hom eQ.hom f)

/- Lemma 4.40.3 (2), comparison existence: two inducing `1`-morphisms admit a `2`-isomorphism.
-/
@[stacks 04SF "(2) comparison existence"]
#check (FiberedCategoryOver.Groupoids.InducesHom.nonempty_iso eP eQ f hF hG :
  Nonempty (F ≅ G))

/- Lemma 4.40.3 (2), comparison uniqueness: the `2`-isomorphism between two inducing
`1`-morphisms is unique. -/
@[stacks 04SF "(2) comparison uniqueness"]
#check (FiberedCategoryOver.Groupoids.InducesHom.subsingleton_iso eP eQ f hF hG :
  Subsingleton (F ≅ G))

end CategoryTheory
