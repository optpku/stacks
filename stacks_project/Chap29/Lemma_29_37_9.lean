module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative.BaseChange
import StacksCheckRecall

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

universe u

/- Lemma 29.37.9: relative ampleness is preserved by base change around a cartesian square. -/
@[stacks 0893] #check
  (AlgebraicGeometry.RelativelyAmple.of_isPullback :
    ∀ {S X S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
      {g' : X' ⟶ X} {f' : X' ⟶ S'} {L : X.Modules},
      IsPullback g' f' f g → RelativelyAmple f L →
        RelativelyAmple f' ((Scheme.Modules.pullback g').obj L))
