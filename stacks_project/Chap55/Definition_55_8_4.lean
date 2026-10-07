module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.MinimalModel
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Hom

/- Definition 55.8.4: a minimal model is a regular proper model with no exceptional curve of the
first kind. -/
@[stacks 0C2V] #check (AlgebraicGeometry.Scheme.Hom.IsMinimalModel :
  {R : Type u} → [CommRing R] → [IsDomain R] → [IsDiscreteValuationRing R] →
    {X : Scheme.{u}} → (X ⟶ Spec (CommRingCat.of R)) → Prop)

end AlgebraicGeometry.Scheme.Hom
