module

public import Mathlib.CategoryTheory.Sites.Over
public import ReasLib.AlgebraicGeometry.RingedSite.Basic
public import Mathlib.Tactic.CrossRefAttribute

@[expose] public section

/-!
# Localized ringed sites

This module owns the ringed site obtained by restricting a ringed site to the slice over one of
its objects.
-/

open CategoryTheory

noncomputable section

universe u v w

namespace RingedSite

/-- The localization of a ringed site at `U`, with carrier `C / U`,
slice topology `J.over U`, and restricted structure sheaf `𝒪.over U`. -/
@[stacks 04IX "(1)"]
abbrev localization (X : RingedSite.{u, v, w}) (U : X.carrier) :
    RingedSite.{max u v, v, w} :=
  RingedSite.ofRingSheaf (X.siteTopology.over U) (X.structureSheaf.over U)


end RingedSite
