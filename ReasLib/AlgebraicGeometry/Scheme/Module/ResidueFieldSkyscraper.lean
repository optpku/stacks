module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Skyscraper

@[expose] public section

universe u

open CategoryTheory.Limits
open AlgebraicGeometry.RingedSpace.Module

namespace AlgebraicGeometry.Scheme.Modules

/-- The skyscraper module on a scheme at a point, with value the residue field of its
local ring. -/
noncomputable def residueFieldSkyscraper {X : Scheme.{u}} (x : X) : X.Modules :=
  Skyscraper.atPoint x
    (ModuleCat.of (RingCat.of (X.presheaf.stalk x))
      (IsLocalRing.ResidueField (X.presheaf.stalk x)))

/-- The residue-field skyscraper is the skyscraper of the stalk's residue-field module. -/
theorem residueFieldSkyscraper_spec {X : Scheme.{u}} (x : X) :
    residueFieldSkyscraper x =
      Skyscraper.atPoint x
        (ModuleCat.of (RingCat.of (X.presheaf.stalk x))
          (IsLocalRing.ResidueField (X.presheaf.stalk x))) := rfl

/-- The finite coproduct of residue-field skyscraper modules at an explicit family of
points of a scheme. -/
noncomputable def residueFieldSkyscraperCoproduct {X : Scheme.{u}}
    {r : ℕ} (c : Fin r → X) : X.Modules :=
  ∐ fun i ↦ residueFieldSkyscraper (c i)

/-- The residue-field skyscraper coproduct is the categorical coproduct of the modules
supported at the supplied points. -/
theorem residueFieldSkyscraperCoproduct_spec {X : Scheme.{u}}
    {r : ℕ} (c : Fin r → X) :
    residueFieldSkyscraperCoproduct c = ∐ fun i ↦ residueFieldSkyscraper (c i) := rfl

end AlgebraicGeometry.Scheme.Modules
