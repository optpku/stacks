module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.QuasiFinite.Fiber
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

/- Lemma 67.27.9: If `S` is a scheme and `f : X ⟶ Y` is a finite-type morphism
of algebraic spaces over `S`, then for every `y` in `Points Y` the set of
points of `Points X` lying over `y` at which `f` is quasi-finite is finite. -/
@[stacks 0ABN] #check
  (AlgebraicGeometry.AlgebraicSpace.FiniteType.finiteQuasiFiniteAtPointsOver :
    ∀ {S : AlgebraicGeometry.Scheme.{u}} {X Y : AlgebraicGeometry.AlgebraicSpace S}
      (f : X ⟶ Y) [AlgebraicGeometry.AlgebraicSpace.FiniteType f]
      (y : AlgebraicGeometry.AlgebraicSpace.Points Y),
      (setOf fun x : AlgebraicGeometry.AlgebraicSpace.Points X ↦
        AlgebraicGeometry.AlgebraicSpace.Points.map f x = y ∧
          AlgebraicGeometry.AlgebraicSpace.QuasiFiniteAt f x).Finite)
