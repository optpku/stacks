/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Jacobson
public import Mathlib.CategoryTheory.ObjectProperty.SiteLocal
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Smooth.Basic

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.JacobsonSpace

/-- The Jacobson-space property for schemes is local for the smooth precoverage. -/
instance smoothLocal :
    ObjectProperty.IsLocal
      (fun X : Scheme.{u} ↦ JacobsonSpace X) Scheme.bigSmoothPrecoverage := sorry

end AlgebraicGeometry.Scheme.JacobsonSpace
