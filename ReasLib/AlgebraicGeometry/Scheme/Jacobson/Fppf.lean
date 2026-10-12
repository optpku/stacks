/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Jacobson
public import ReasLib.AlgebraicGeometry.Scheme.ObjectProperty.AffineDescent

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme.JacobsonSpace

/-- The Jacobson-space property for schemes is local for the fppf precoverage. -/
instance isLocalFppf :
    CategoryTheory.ObjectProperty.IsLocal
      (fun X : Scheme.{u} ↦ JacobsonSpace X) Scheme.fppfPrecoverage := sorry

end AlgebraicGeometry.Scheme.JacobsonSpace
