module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.CycleGroup.Basic

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

universe u

/- The canonical additive subgroup of cycles of degree `k`, retained as a typed
compatibility bridge for imports of this module. -/
#check (AlgebraicGeometry.AlgebraicSpace.Hom.cycleGroup :
  ∀ {S : Scheme.{u}} {B X : AlgebraicSpace S} (f : X ⟶ B) [LocallyOfFiniteType f]
    (δ : Points B → ℤ) (k : ℤ),
    AddSubgroup (Function.locallyFinsupp (Points X) ℤ))
