/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.CommSq
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import ReasLib.AlgebraicGeometry.RingedSpace.Morphism.Thickening.Strict

/-!
# Commuting chains of thickening squares

The chain only stores morphisms and commuting diagrams. No thickening,
exactness, strictness or flatness assumptions are required to form it.
The vertical maps are morphisms under `X`, bundling their restriction equations.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace.IsFirstOrderThickening

/-- A three-column commuting diagram under a fixed morphism `f`.
The nine fields are seven morphisms and the two remaining square equations. -/
structure ThickeningSquareChain
    {X S X1 X2 X3 S1 S2 S3 : RingedSpace.{u}}
    (f : X ⟶ S) (i1 : X ⟶ X1) (i2 : X ⟶ X2) (i3 : X ⟶ X3)
    (t1 : S ⟶ S1) (t2 : S ⟶ S2) (t3 : S ⟶ S3) where
  /-- The first arrow of the top row, under `X`. -/
  h : Under.mk i1 ⟶ Under.mk i2
  /-- The second arrow of the top row, under `X`. -/
  k : Under.mk i2 ⟶ Under.mk i3
  /-- The first arrow of the bottom row, under `S`. -/
  base : Under.mk t1 ⟶ Under.mk t2
  /-- The second arrow of the bottom row, under `S`. -/
  base' : Under.mk t2 ⟶ Under.mk t3
  /-- The first vertical arrow, with its restriction equation. -/
  vertical1 : Under.mk i1 ⟶ Under.mk (f ≫ t1)
  /-- The middle vertical arrow, with its restriction equation. -/
  vertical2 : Under.mk i2 ⟶ Under.mk (f ≫ t2)
  /-- The third vertical arrow, with its restriction equation. -/
  vertical3 : Under.mk i3 ⟶ Under.mk (f ≫ t3)
  /-- The left thickened square commutes. -/
  comm_thick : h.right ≫ vertical2.right = vertical1.right ≫ base.right
  /-- The right thickened square commutes. -/
  comm_thick' : k.right ≫ vertical3.right = vertical2.right ≫ base'.right

namespace ThickeningSquareChain

variable {X S X1 X2 X3 S1 S2 S3 : RingedSpace.{u}}
variable {f : X ⟶ S} {i1 : X ⟶ X1} {i2 : X ⟶ X2} {i3 : X ⟶ X3}
variable {t1 : S ⟶ S1} {t2 : S ⟶ S2} {t3 : S ⟶ S3}

/-- The ambient map in column 1. -/
abbrev f1' (C : ThickeningSquareChain f i1 i2 i3 t1 t2 t3) : X1 ⟶ S1 :=
  C.vertical1.right

/-- The restriction equation in column 1. -/
theorem comm1 (C : ThickeningSquareChain f i1 i2 i3 t1 t2 t3) :
    i1 ≫ C.f1' = f ≫ t1 := C.vertical1.w

/-- The ambient map in column 2. -/
abbrev f2' (C : ThickeningSquareChain f i1 i2 i3 t1 t2 t3) : X2 ⟶ S2 :=
  C.vertical2.right

/-- The restriction equation in column 2. -/
theorem comm2 (C : ThickeningSquareChain f i1 i2 i3 t1 t2 t3) :
    i2 ≫ C.f2' = f ≫ t2 := C.vertical2.w

/-- The ambient map in column 3. -/
abbrev f3' (C : ThickeningSquareChain f i1 i2 i3 t1 t2 t3) : X3 ⟶ S3 :=
  C.vertical3.right

/-- The restriction equation in column 3. -/
theorem comm3 (C : ThickeningSquareChain f i1 i2 i3 t1 t2 t3) :
    i3 ≫ C.f3' = f ≫ t3 := C.vertical3.w

/-- All three vertical maps restrict to the fixed base morphism. -/
theorem restricts (C : ThickeningSquareChain f i1 i2 i3 t1 t2 t3) :
    CommSq i1 f C.f1' t1 ∧ CommSq i2 f C.f2' t2 ∧ CommSq i3 f C.f3' t3 :=
  ⟨⟨C.comm1⟩, ⟨C.comm2⟩, ⟨C.comm3⟩⟩

/-- The squares between the two rows commute. -/
theorem thickenedSq (C : ThickeningSquareChain f i1 i2 i3 t1 t2 t3) :
    CommSq C.h.right C.f1' C.f2' C.base.right ∧
      CommSq C.k.right C.f2' C.f3' C.base'.right :=
  ⟨⟨C.comm_thick⟩, ⟨C.comm_thick'⟩⟩

/-- Column 1 as a morphism of thickenings; only this column must be a thickening. -/
def thickeningHom1 [IsThickening i1] [IsThickening t1]
    (C : ThickeningSquareChain f i1 i2 i3 t1 t2 t3) :
    Thickening.of i1 ⟶ Thickening.of t1 :=
  Thickening.homMk f C.f1' C.comm1.symm

/-- Column 2 as a morphism of thickenings; only this column must be a thickening. -/
def thickeningHom2 [IsThickening i2] [IsThickening t2]
    (C : ThickeningSquareChain f i1 i2 i3 t1 t2 t3) :
    Thickening.of i2 ⟶ Thickening.of t2 :=
  Thickening.homMk f C.f2' C.comm2.symm

/-- Column 3 as a morphism of thickenings; only this column must be a thickening. -/
def thickeningHom3 [IsThickening i3] [IsThickening t3]
    (C : ThickeningSquareChain f i1 i2 i3 t1 t2 t3) :
    Thickening.of i3 ⟶ Thickening.of t3 :=
  Thickening.homMk f C.f3' C.comm3.symm

end ThickeningSquareChain

end AlgebraicGeometry.RingedSpace.IsFirstOrderThickening
