module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Thickening
import StacksCheckRecall

open CategoryTheory AlgebraicGeometry

universe u

/- Lemma 76.9.9: If `X ⟶ X'` and `X' ⟶ X''` are thickenings of algebraic spaces
over a scheme `S`, then the composite `X ⟶ X''` is a thickening. -/
@[stacks 0BPH] #check
  (AlgebraicGeometry.AlgebraicSpace.thickening_comp :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y Z : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y) (g : Y ⟶ Z)
      (hf : AlgebraicGeometry.AlgebraicSpace.thickening f)
      (hg : AlgebraicGeometry.AlgebraicSpace.thickening g),
      AlgebraicGeometry.AlgebraicSpace.thickening (f ≫ g))
