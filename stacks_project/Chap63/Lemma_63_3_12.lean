module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.LowerShriek.BaseChange
import StacksCheckRecall

/-!
# Base change for underived étale lower shriek

Lemma 63.3.12: in a cartesian square of schemes with `f` separated and locally
of finite type, underived compact-support pushforward commutes with étale
inverse image.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Functor
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale
open AlgebraicGeometry.Scheme.Hom

noncomputable section

universe u

/- Lemma 63.3.12: In a cartesian square of schemes with `f` separated and
locally of finite type, compact-support pushforward commutes with inverse image
for every abelian sheaf on the small étale site of `X`. -/
@[stacks 0F55] #check
  (AlgebraicGeometry.Scheme.Etale.etaleLowerShriekBaseChange_isIso_of_isPullback :
    ∀ {X Y X' Y' : Scheme.{u}}
      (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
      (h_cart : IsPullback g' f' f g) [IsSeparated f] [LocallyOfFiniteType f],
      -- Local instance justification (proof-local temporary data): the explicit cartesian square derives this property of f' from f; it is not an additional assumption.
      letI : IsSeparated f' :=
        MorphismProperty.of_isPullback (P := @IsSeparated) h_cart inferInstance
      -- Local instance justification (proof-local temporary data): the explicit cartesian square derives this property of f' from f; it is not an additional assumption.
      letI : LocallyOfFiniteType f' :=
        MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) h_cart inferInstance
      IsIso (etaleLowerShriekBaseChange f g f' g' h_cart))

end
