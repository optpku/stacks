module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.ObjectProperty.SiteLocal

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsReduced

/-- Reducedness of schemes is local for the étale precoverage. -/
instance isLocalEtale :
    ObjectProperty.IsLocal
      (AlgebraicGeometry.IsReduced : ObjectProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.etalePrecoverage := sorry

end AlgebraicGeometry.IsReduced
