module

import stacks_project.Chap97.«97_10_0_2_Morphism»
import stacks_project.Chap97.«97_10_0_2_Presheaf»
import StacksCheckRecall

/- 97.10.0.2: For morphisms `Z ⟶ B` and `X ⟶ B` of algebraic spaces over a
scheme `S`, `Mor_B(Z, X)` is the functor `(Over S)ᵒᵖ ⥤ Type (u + 1)` sending a
scheme `T` over `S` to the type of pairs `(a, b)` with `a : ofOver T ⟶ B` and
`b` a morphism over `ofOver T` from `pullback a Z.hom` to `pullback a X.hom`. -/
@[stacks 05Y2] #check AlgebraicGeometry.AlgebraicSpace.RelativeHom.functor
