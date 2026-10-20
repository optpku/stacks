module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.UpperShriek.LocallyQuasiFinite.BaseChange
import StacksCheckRecall

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.Etale AlgebraicGeometry.Scheme.Hom

universe u

/- Lemma 63.6.5. For a cartesian square of schemes with locally quasi-finite
vertical morphisms in the locally finite-type convention, upper shriek commutes
naturally with pushforward on abelian étale sheaves. -/
@[stacks 0F6U] #check (AlgebraicGeometry.Scheme.Etale.upperShriekBaseChangeIso :
  ∀ {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
    (h_cart : IsPullback g' f' f g)
    [LocallyQuasiFinite f] [LocallyOfFiniteType f]
    [LocallyQuasiFinite f'] [LocallyOfFiniteType f'],
    upperShriek f' ⋙ smallEtalePushforwardAb g' ≅
      smallEtalePushforwardAb g ⋙ upperShriek f)
