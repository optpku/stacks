module

public import stacks_project.Chap66.Definition_66_18_9_FMap
public import stacks_project.Chap66.Definition_66_18_9_Square
import StacksCheckRecall

@[expose] public section

/- Definition 66.18.9: for a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`, an
`f`-map `φ : 𝒢 ⟶ ℱ` of sheaves of sets on the small étale sites is a family of maps
`𝒢.obj.obj (op V) ⟶ ℱ.obj.obj (op U)` indexed by commutative squares of schemes `U → X`,
`V → Y`, `U → V` over `f`, compatible with restriction along morphisms in `smallEtaleSite X`
and `smallEtaleSite Y`. -/
@[stacks 03G3] #check AlgebraicGeometry.AlgebraicSpace.FMap
