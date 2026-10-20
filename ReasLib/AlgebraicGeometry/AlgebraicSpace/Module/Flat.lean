/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.FlatOver.BaseChange

/-!
# Flat modules on algebraic spaces

An `𝒪_X`-module on an algebraic space is flat when it is relatively flat over `X`
along the identity morphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicSpace

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

/-- An `𝒪_X`-module on an algebraic space is flat when it is flat over `X` along
the identity morphism. -/
class IsFlat {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) : Prop where
  /-- Absolute flatness is relative flatness along `𝟙 X`. -/
  flatOver_id : flatOver F (𝟙 X)

/-- Absolute flatness of an `𝒪_X`-module is equivalent to relative flatness along `𝟙 X`. -/
theorem isFlat_iff_flatOver_id {S : Scheme.{u}} {X : AlgebraicSpace S} (F : X.Modules) :
    IsFlat F ↔ flatOver F (𝟙 X) := sorry

/-- The structure sheaf of an algebraic space is a flat module. -/
instance unit_isFlat {S : Scheme.{u}} (X : AlgebraicSpace S) :
    IsFlat (SheafOfModules.unit (structureSheaf X)) := sorry

end AlgebraicGeometry.AlgebraicSpace.Modules
