module

public import ReasLib.AlgebraicGeometry.SimplicialScheme.Zariski
public import ReasLib.AlgebraicGeometry.RingedSite.Basic

/-!
# Zariski ringed site of a simplicial scheme

The identity-degree Zariski site of the underlying simplicial space of a simplicial scheme,
equipped with the sheaf of rings assembled from the stagewise structure sheaves.
-/

@[expose] public section

open CategoryTheory CategoryTheory.SimplicialObject Opposite AlgebraicGeometry
open TopologicalSpace TopCat

noncomputable section

universe u

namespace AlgebraicGeometry.SimplicialObject

/-- The Zariski ringed site `U_Zar` of a simplicial scheme. -/
abbrev zariskiRingedSite (U : SimplicialObject Scheme.{u}) : RingedSite :=
  RingedSite.ofRingSheaf (zariskiTopology (forgetToTop.obj U)) (structureSheaf U)

/-- The structure sheaf of `zariskiRingedSite U` is `structureSheaf U`. -/
theorem zariskiRingedSite_structureSheaf (U : SimplicialObject Scheme.{u}) :
    (zariskiRingedSite U).structureSheaf = structureSheaf U :=
  rfl

end AlgebraicGeometry.SimplicialObject
