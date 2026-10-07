module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Smooth.Cancellation
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 37.13.12: for scheme morphisms `f : X ⟶ Y` and `g : Y ⟶ Z`, smoothness of
the composite and étaleness of `g` imply smoothness of `f`. -/
@[stacks 0G80] #check
  (AlgebraicGeometry.Smooth.of_comp :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      [AlgebraicGeometry.Smooth (f ≫ g)] [AlgebraicGeometry.Etale g],
      AlgebraicGeometry.Smooth f)
