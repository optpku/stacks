/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Relative
public import ReasLib.AlgebraicGeometry.Scheme.Module.Ample.Tensor
public import ReasLib.AlgebraicGeometry.Scheme.Module.Pullback.Monoidal

/-!
# Relative Ampleness and Tensor Products

This file records eventual absolute ampleness after tensoring a relatively ample module with
high tensor powers pulled back from the base.
-/

@[expose] public section

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/-- Tensoring a relatively ample module with sufficiently high pulled-back tensor powers of an
ample invertible module on the base produces an ample invertible module. -/
theorem RelativelyAmple.eventually_isAmpleObject_tensor_pullback_tensorPow
    {X Y : Scheme.{u}} {f : X ⟶ Y} {L : X.Modules} {M : Y.Modules}
    (hL : RelativelyAmple f L) (hM : Scheme.Modules.isAmpleObject M) :
    ∀ᶠ a : ℕ in Filter.atTop,
      Scheme.Modules.isAmpleObject
        (L ⊗ (Scheme.Modules.pullback f).obj (RingedSpace.TensorPower.sheaf M a)) := sorry

end AlgebraicGeometry
