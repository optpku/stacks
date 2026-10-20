/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DescentData.Etale

open CategoryTheory

universe u

#check
  (AlgebraicGeometry.Scheme.DescentData.Etale.canonicalFunctor :
    ∀ {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S),
      S.Etale ⥤ AlgebraicGeometry.Scheme.DescentData.Etale f)
