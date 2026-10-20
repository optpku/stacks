module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.Cancellation
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- Lemma 67.23.6: if `g ∘ f` is locally of finite type then so is `f`. -/
@[stacks 0462] #check
  (AlgebraicGeometry.AlgebraicSpace.LocallyOfFiniteType.of_comp :
    ∀ {S : Scheme.{u}} {X Y Z : AlgebraicSpace S} (f : X ⟶ Y) (g : Y ⟶ Z)
      [LocallyOfFiniteType (f ≫ g)], LocallyOfFiniteType f)
