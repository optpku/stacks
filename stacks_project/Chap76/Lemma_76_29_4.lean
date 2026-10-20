module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Fiber.GeometricallyReduced.Constructible
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- Lemma 76.29.4: Let `S` be a scheme. Let `f : X ⟶ Y` be a morphism of algebraic spaces
over `S` which is quasi-compact and locally of finite presentation. Then the set
`E = geometricallyReducedFiberLocus f` of points of `|Y|` at which the fibre of `f` is
geometrically reduced is étale locally constructible. -/
@[stacks 0E0A] #check
  (AlgebraicGeometry.AlgebraicSpace.isEtaleLocallyConstructible_geometricallyReducedFiberLocus :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
      [QuasiCompact f] [LocallyOfFinitePresentation f],
      IsEtaleLocallyConstructible (geometricallyReducedFiberLocus f))

end AlgebraicGeometry.AlgebraicSpace
