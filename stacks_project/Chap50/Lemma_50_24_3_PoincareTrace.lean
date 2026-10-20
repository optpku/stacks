/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.PoincareDuality.Forms

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed TopologicalSpace
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

#check (AlgebraicGeometry.Scheme.DeRham.pushforwardForm :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) (p : ℕ),
    RingedSpace.ModuleDerived S.toRingedSpace)

end AlgebraicGeometry.Scheme.DeRham
