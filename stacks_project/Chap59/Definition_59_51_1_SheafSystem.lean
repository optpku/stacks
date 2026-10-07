module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SheafSystem

universe uI u

#check (AlgebraicGeometry.Scheme.Etale.SheafSystem :
  {I : Type uI} → [Preorder I] →
    CategoryTheory.PreorderInverseSystem I AlgebraicGeometry.Scheme.{u} →
      Type (max (u + 2) uI))
