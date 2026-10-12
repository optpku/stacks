/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.Locality
public import ReasLib.AlgebraicGeometry.Scheme.Normal.Nagata.FiniteType
public import ReasLib.RingTheory.Normal.Nagata.Smooth
public import Mathlib.CategoryTheory.ObjectProperty.SiteLocal
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Basic

/-!
# Smooth-locality of Nagata schemes

This file records that the Nagata property for schemes is local for smooth covers.
-/

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.Nagata

/-- The Nagata property for schemes is local for the smooth precoverage. -/
@[stacks 036E]
instance smoothLocal :
    CategoryTheory.ObjectProperty.IsLocal
      (AlgebraicGeometry.Scheme.Nagata :
        CategoryTheory.ObjectProperty AlgebraicGeometry.Scheme.{u})
      AlgebraicGeometry.Scheme.bigSmoothPrecoverage := sorry

end AlgebraicGeometry.Scheme.Nagata
