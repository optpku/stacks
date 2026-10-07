module

import StacksCheckRecall
import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiberDegree.BaseChange

open CategoryTheory Limits

universe u

#check
  (AlgebraicGeometry.Scheme.Hom.degreesOfFibresBoundedBy_of_surjective_baseChange :
    ∀ {X Y Y' : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ Y) (g : Y' ⟶ Y) [AlgebraicGeometry.Surjective g] {n : ℕ},
      AlgebraicGeometry.Scheme.Hom.degreesOfFibresBoundedBy (pullback.snd f g) n →
        AlgebraicGeometry.Scheme.Hom.degreesOfFibresBoundedBy f n)

/- Lemma 29.57.6: universal boundedness of fibre degrees descends along a surjective
base change. -/
@[stacks 03J8] #check
  (AlgebraicGeometry.Scheme.Hom.universallyBoundedFibres_of_surjective_baseChange :
    ∀ {X Y Y' : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ Y) (g : Y' ⟶ Y) [AlgebraicGeometry.Surjective g],
      AlgebraicGeometry.Scheme.Hom.universallyBoundedFibres (pullback.snd f g) →
        AlgebraicGeometry.Scheme.Hom.universallyBoundedFibres f)
