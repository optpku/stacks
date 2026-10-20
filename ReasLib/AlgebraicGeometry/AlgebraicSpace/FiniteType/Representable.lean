/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FiniteType
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

/-! # Finite type morphisms of represented algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of representable algebraic spaces over `S` is locally of finite type if
and only if the representing morphism of schemes is locally of finite type. -/
theorem locallyOfFiniteType_ofOverMap_iff {S : Scheme.{u}} {X0 Y0 : Over S}
    (f0 : X0 ⟶ Y0) :
    LocallyOfFiniteType (ofOverMap f0) ↔
      AlgebraicGeometry.LocallyOfFiniteType f0.left :=
  sorry

/-- Local finite type of `ofOverMap f0` yields local finite type of the underlying
scheme morphism `f0.left`. -/
instance instLocallyOfFiniteType_left_ofOverMap {S : Scheme.{u}} {X0 Y0 : Over S}
    (f0 : X0 ⟶ Y0) [LocallyOfFiniteType (ofOverMap f0)] :
    AlgebraicGeometry.LocallyOfFiniteType f0.left :=
  (locallyOfFiniteType_ofOverMap_iff f0).mp inferInstance

/-- A locally finite type scheme morphism over the base induces a locally finite type
morphism of algebraic spaces. -/
instance instLocallyOfFiniteType_ofOverMap {S : Scheme.{u}} {X0 Y0 : Over S}
    (f0 : X0 ⟶ Y0) [AlgebraicGeometry.LocallyOfFiniteType f0.left] :
    LocallyOfFiniteType (ofOverMap f0) :=
  (locallyOfFiniteType_ofOverMap_iff f0).mpr inferInstance

end AlgebraicGeometry.AlgebraicSpace
