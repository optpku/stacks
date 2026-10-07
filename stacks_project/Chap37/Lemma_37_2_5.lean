module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Thickening
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

/- Lemma 37.2.5: the composite of two thickenings is a thickening. -/
@[stacks 0BPE] #check
  (AlgebraicGeometry.IsThickening.comp :
    ∀ {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
      [AlgebraicGeometry.IsThickening f] [AlgebraicGeometry.IsThickening g],
      AlgebraicGeometry.IsThickening (f ≫ g))
