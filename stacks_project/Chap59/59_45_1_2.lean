module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Etale
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.UniversalHomeomorphism
import StacksCheckRecall

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

variable {S' S : Scheme.{u}} (f : S' ⟶ S) [UniversalHomeomorphism f]

/- 59.45.1.2: Base change along a universal homeomorphism `S' ⟶ S` sends a scheme
étale over `S` to singleton descent data relative to `S'/S` whose component is étale
over `S'`. -/
@[stacks 0BU0] #check
  (AlgebraicGeometry.Scheme.DescentData.Etale.canonicalFunctor f :
    S.Etale ⥤ AlgebraicGeometry.Scheme.DescentData.Etale f)
