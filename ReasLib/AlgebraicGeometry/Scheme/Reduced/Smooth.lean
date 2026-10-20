module

public import ReasLib.AlgebraicGeometry.Scheme.Reduced
public import Mathlib.CategoryTheory.ObjectProperty.SiteLocal
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Basic
public import ReasLib.RingTheory.Smooth.Reduced
public import ReasLib.RingTheory.RingHom.FaithfullyFlat.Reduced

/-!
# Smooth-locality of reduced schemes

This file records that reducedness of schemes is local for smooth covers.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.IsReduced

/-- Reducedness of schemes is local for the smooth precoverage. -/
@[stacks 034E, instance]
instance smoothLocal :
    CategoryTheory.ObjectProperty.IsLocal
      (AlgebraicGeometry.IsReduced :
        CategoryTheory.ObjectProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSmoothPrecoverage := sorry

end AlgebraicGeometry.IsReduced
