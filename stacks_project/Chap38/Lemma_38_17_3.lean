module

public import ReasLib.AlgebraicGeometry.Scheme.Module.AssociatedPoints.Purity.GeometricallyIntegral

import StacksCheckRecall

@[expose] public section

open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 38.17.3: a finite type flat morphism with geometrically integral fibres has universally
pure structure sheaf over its base. -/
@[stacks 05K5] #check
  (AlgebraicGeometry.Scheme.isUniversallyPureOver_of_flat_of_geometricallyIntegral :
    ∀ {X S : Scheme.{u}} (f : X ⟶ S) [Hom.FiniteType f] [Flat f]
      [GeometricallyIntegral f],
    Modules.IsUniversallyPureOver
      (SheafOfModules.unit X.ringCatSheaf : X.Modules) f)

end AlgebraicGeometry.Scheme
