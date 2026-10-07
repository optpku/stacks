module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree.FiniteLocallyFree

universe u

/- Lemma 29.57.3: if `f` is a finite locally free morphism of degree `d`, then `d`
bounds the degree of the fibres of `f`. -/
@[stacks 0CC2]
#check (AlgebraicGeometry.Scheme.Hom.degreesOfFibresBoundedBy_of_isFiniteLocallyFreeOfRank :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (d : ℕ)
    [AlgebraicGeometry.IsFiniteLocallyFreeOfRank f d],
    AlgebraicGeometry.Scheme.Hom.degreesOfFibresBoundedBy f d)
