module

public import ReasLib.AlgebraicGeometry.Scheme.SerreCondition.Regular
public import ReasLib.AlgebraicGeometry.Scheme.SerreCondition.Smooth

/-!
# Smooth-locality of regular schemes

This file records that regularity of schemes is local for the smooth precoverage.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Regular

/-- Regularity of schemes is local for the smooth precoverage. -/
instance smoothLocal :
    ObjectProperty.IsLocal (AlgebraicGeometry.Scheme.Regular : ObjectProperty Scheme.{u})
      AlgebraicGeometry.Scheme.bigSmoothPrecoverage := sorry

end AlgebraicGeometry.Scheme.Regular
