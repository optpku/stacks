module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 29.37.3: if a morphism of schemes admits a relatively ample invertible sheaf, then it is
separated. -/
@[stacks 01VI] #check
  (AlgebraicGeometry.isSeparated_of_exists_relativelyAmple :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      (∃ L : X.Modules, AlgebraicGeometry.RelativelyAmple f L) →
        AlgebraicGeometry.IsSeparated f)
