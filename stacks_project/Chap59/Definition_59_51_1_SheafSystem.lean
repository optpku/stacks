/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SheafSystem

universe uI u

#check (AlgebraicGeometry.Scheme.Etale.SheafSystem :
  {I : Type uI} → [Preorder I] →
    CategoryTheory.PreorderInverseSystem I AlgebraicGeometry.Scheme.{u} →
      Type (max (u + 2) uI))
