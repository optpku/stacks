/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.ObjectProperty.SiteLocal
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Basic
public import ReasLib.RingTheory.RingHom.FaithfullyFlat.Noetherian

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.IsLocallyNoetherian

/-- Local Noetherianity of schemes is local for the smooth precoverage. -/
instance smoothLocal :
    ObjectProperty.IsLocal
      (AlgebraicGeometry.IsLocallyNoetherian : ObjectProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSmoothPrecoverage := sorry

end AlgebraicGeometry.IsLocallyNoetherian
