module

public import ReasLib.AlgebraicGeometry.RingedSpace.Module.CotangentComplex.Transitivity
import StacksCheckRecall

open CategoryTheory
open CategoryTheory.Pretriangulated

universe u

/- Lemma 92.20.3. For composable morphisms of ringed spaces, the canonical triangle
of cotangent complexes, with derived inverse image as its first vertex, is distinguished. -/
@[stacks 08T4] #check (AlgebraicGeometry.RingedSpace.transitivityTriangle_distinguished :
  ∀ {X Y Z : AlgebraicGeometry.RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z),
    AlgebraicGeometry.RingedSpace.transitivityTriangle f g ∈
      distTriang (DerivedCategory X.Modules))
