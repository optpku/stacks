module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.11.2: A composition of formally smooth morphisms is formally smooth. -/
@[stacks 02H1] #check
  (AlgebraicGeometry.FormallySmooth.comp :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      [AlgebraicGeometry.FormallySmooth f] [AlgebraicGeometry.FormallySmooth g],
      AlgebraicGeometry.FormallySmooth (f ≫ g))
