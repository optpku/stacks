/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.ObjectProperty.SiteLocal

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsLocallyNoetherian

/-- Local Noetherianity of schemes is local for the étale precoverage. -/
instance isLocalEtale :
    ObjectProperty.IsLocal
      (AlgebraicGeometry.IsLocallyNoetherian : ObjectProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.etalePrecoverage := sorry

end AlgebraicGeometry.IsLocallyNoetherian
