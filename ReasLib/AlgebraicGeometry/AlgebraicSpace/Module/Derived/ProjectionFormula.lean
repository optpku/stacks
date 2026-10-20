/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Pullback.Tensor
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Derived.Adjunction

/-! # The canonical derived projection-formula mate -/

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory CategoryTheory.Limits
open CategoryTheory.DerivedCategory CategoryTheory.Functor
open CategoryTheory.MonoidalCategory ComplexShape

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
variable {S : Scheme.{u}}

/-- The canonical projection-formula mate
`Rf_* E ⊗^L K ⟶ Rf_*(E ⊗^L Lf^* K)` on unbounded derived modules. -/
noncomputable def leftMate {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (E : ModuleDerived X) (K : ModuleDerived Y) :
    (DerivedTensor.Right.functor K).obj ((Modules.moduleDerivedPushforward f).obj E) ⟶
      (Modules.moduleDerivedPushforward f).obj
        ((DerivedTensor.Right.functor ((LeftDerived.Homotopy.functor (Modules.pullback f)).obj K)).obj E) :=
  (Modules.derivedPullbackPushforwardAdjunction f).homEquiv _ _
    (rightTensorComparison f ((Modules.moduleDerivedPushforward f).obj E) K ≫
      (DerivedTensor.Right.functor ((LeftDerived.Homotopy.functor (Modules.pullback f)).obj K)).map
        ((Modules.derivedPullbackPushforwardAdjunction f).counit.app E))

/-- Transposing `leftMate` along `Lf^* ⊣ Rf_*` recovers the derived pullback-tensor comparison
of `Rf_* E ⊗^L K` followed by the fixed-right tensor of the counit `Lf^* Rf_* E ⟶ E`. -/
theorem leftMate_spec {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (E : ModuleDerived X) (K : ModuleDerived Y) :
    ((Modules.derivedPullbackPushforwardAdjunction f).homEquiv _ _).symm (leftMate f E K) =
      rightTensorComparison f ((Modules.moduleDerivedPushforward f).obj E) K ≫
        (DerivedTensor.Right.functor ((LeftDerived.Homotopy.functor (Modules.pullback f)).obj K)).map
          ((Modules.derivedPullbackPushforwardAdjunction f).counit.app E) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.DerivedQCoh
