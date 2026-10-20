module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSite.FMap
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Definition 66.18.9: for a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S`, an
`f`-map `φ : 𝒢 ⟶ ℱ` of sheaves of sets on the small étale sites is a family of maps
`𝒢.obj.obj (op V) ⟶ ℱ.obj.obj (op U)` indexed by commutative squares of schemes `U → X`,
`V → Y`, `U → V` over `f`, compatible with restriction along morphisms in `smallEtaleSite X`
and `smallEtaleSite Y`. -/
@[stacks 03G3] #check (AlgebraicGeometry.AlgebraicSpace.FMap :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (𝒢 : Sheaf (AlgebraicSpace.smallEtaleTopology Y) (Type (u + 1)))
    (ℱ : Sheaf (AlgebraicSpace.smallEtaleTopology X) (Type (u + 1))), Type (u + 1))
