module

public import ReasLib.AlgebraicGeometry.RingedSite.Localization.Simplicial

/-!
# Ringed total localization of a simplicial semi-representable object

The ringed total localization and its degree morphisms are available through this
compatibility import.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped SemiRepresentableFamily Simplicial

universe ι u v w

variable {X : RingedSite.{u, v, w}}
variable (K : SimplicialObject (FormalCoproduct.{ι} X.carrier))

#check (RingedSite.Localization.AtSimplicialSR.site K :
  RingedSite.{max ι u v, max ι u v, w})

#check (RingedSite.Localization.AtSimplicialSR.structureSheaf_spec K :
  (RingedSite.Localization.AtSimplicialSR.site K).structureSheaf =
    RingedSite.Localization.AtSimplicialSR.ringSheaf K)
