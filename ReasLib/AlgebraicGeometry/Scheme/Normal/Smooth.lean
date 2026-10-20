module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Locality
public import Mathlib.CategoryTheory.ObjectProperty.SiteLocal
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Basic
public import ReasLib.RingTheory.RingHom.FaithfullyFlat.Normal
public import ReasLib.RingTheory.Smooth.Normal

/-!
# Smooth-locality of normal schemes

This file records that normality of schemes is local for smooth covers.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.isNormal

/-- Normality of schemes is local for the smooth precoverage. -/
instance smoothLocal :
    CategoryTheory.ObjectProperty.IsLocal
      (AlgebraicGeometry.Scheme.isNormal :
        CategoryTheory.ObjectProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSmoothPrecoverage := sorry

end AlgebraicGeometry.Scheme.isNormal
