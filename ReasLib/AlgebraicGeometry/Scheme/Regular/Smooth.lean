/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

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
