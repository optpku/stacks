module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.RelativeVery.BaseChange
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory

universe u

/- Lemma 29.38.8: let `f : X ⟶ S` be a morphism of schemes and let `L` be a relatively very
ample module for `f`. For any cartesian square from `f' : X' ⟶ S'` to `f`, the pullback of `L`
to `X'` is relatively very ample for `f'`. -/
@[stacks 0B3F] #check
  (AlgebraicGeometry.RelativelyVeryAmple.of_isPullback :
    ∀ {S X S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
      {g' : X' ⟶ X} {f' : X' ⟶ S'} {L : X.Modules},
      IsPullback g' f' f g →
        RelativelyVeryAmple f L →
          RelativelyVeryAmple f' ((Scheme.Modules.pullback g').obj L))
