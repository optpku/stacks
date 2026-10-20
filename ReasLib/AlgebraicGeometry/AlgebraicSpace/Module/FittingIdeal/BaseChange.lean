/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FittingIdeal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.IdealSubobject.Pullback

/-!
# Base change of Fitting ideal sheaves on algebraic spaces

Fitting ideals of finite-type quasi-coherent modules commute with inverse image
along arbitrary morphisms of algebraic spaces.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The inverse image of the `i`th Fitting ideal of a finite-type quasi-coherent
module is the `i`th Fitting ideal of its pullback. -/
theorem fittingIdealSheaf_pullback {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (F : Y.Modules) [F.IsFiniteType] [F.IsQuasicoherent] (i : ℕ) :
    (fittingIdealSheaf F i).pullback f =
      fittingIdealSheaf ((Modules.pullback f).obj F) i :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
