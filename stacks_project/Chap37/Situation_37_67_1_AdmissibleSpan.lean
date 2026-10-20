/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Pushout.AdmissibleSpan

open CategoryTheory

universe u

#check (@AlgebraicGeometry.Scheme.Pushout.IsAdmissibleSpan :
  {S : AlgebraicGeometry.Scheme.{u}} →
    {Z X Y : CategoryTheory.Over S} →
      (Z ⟶ X) → (Z ⟶ Y) → Prop)
