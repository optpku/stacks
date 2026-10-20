/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Descent

@[expose] public section

open CategoryTheory

universe u v

#check (@AlgebraicGeometry.Scheme.QCoh.DescentData :
  {I : Type v} → {S : AlgebraicGeometry.Scheme.{u}} →
    (X : I → AlgebraicGeometry.Scheme.{u}) → ((i : I) → X i ⟶ S) →
      Type (max (u + 1) v))
