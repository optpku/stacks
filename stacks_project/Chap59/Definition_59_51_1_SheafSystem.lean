/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.SheafSystem

universe uI u

#check (AlgebraicGeometry.Scheme.Etale.SheafSystem :
  {I : Type uI} → [Preorder I] →
    CategoryTheory.PreorderInverseSystem I AlgebraicGeometry.Scheme.{u} →
      Type (max (u + 2) uI))
