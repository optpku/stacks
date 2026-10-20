module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Submersive
import StacksCheckRecall

@[expose]
public section

open CategoryTheory

universe u

/- Definition 67.7.2 (1): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is submersive if the continuous map `|X| ⟶ |Y|` is a quotient map. -/
@[stacks 0412] #check (AlgebraicGeometry.AlgebraicSpace.Submersive :
  {S : AlgebraicGeometry.Scheme.{u}} → {X Y : AlgebraicGeometry.AlgebraicSpace S} →
    (X ⟶ Y) → Prop)

/- Definition 67.7.2 (2): a morphism `f : X ⟶ Y` of algebraic spaces over a scheme
`S` is universally submersive if for every morphism `Y' ⟶ Y` of algebraic spaces
the base change `Y' ×_Y X ⟶ Y'` is submersive. -/
@[stacks 0412] #check (AlgebraicGeometry.AlgebraicSpace.UniversallySubmersive :
  {S : AlgebraicGeometry.Scheme.{u}} → {X Y : AlgebraicGeometry.AlgebraicSpace S} →
    (X ⟶ Y) → Prop)
