module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Composition
import StacksCheckRecall

open CategoryTheory

universe u

/- Lemma 37.6.3: A composition of formally unramified morphisms is formally unramified. -/
@[stacks 02HA] #check
  (AlgebraicGeometry.FormallyUnramified.comp :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
      AlgebraicGeometry.FormallyUnramified f → AlgebraicGeometry.FormallyUnramified g →
        AlgebraicGeometry.FormallyUnramified (f ≫ g))
