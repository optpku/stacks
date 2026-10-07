module

public import ReasLib.AlgebraicGeometry.Scheme.CohenMacaulay
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.ObjectProperty.SiteLocal

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.CohenMacaulay

/-- Cohen–Macaulayness is local for the étale precoverage. -/
instance isLocalEtale :
    ObjectProperty.IsLocal (Scheme.CohenMacaulay : ObjectProperty Scheme.{u})
      Scheme.etalePrecoverage := sorry

end AlgebraicGeometry.Scheme.CohenMacaulay
