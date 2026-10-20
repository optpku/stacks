/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicStack.Separation
public import ReasLib.AlgebraicGeometry.AlgebraicStack.QuasiSeparated
public import ReasLib.CategoryTheory.Bicategory.Limits.PseudoPullback.PseudoCone.Bilimit
public import ReasLib.CategoryTheory.Fibered.TwoFibreProduct.FullSubbicategory.Basic

/-!
# Quasi-separatedness permanence for algebraic stacks

Morphisms between quasi-separated algebraic stacks are quasi-separated.
Fibre products of quasi-separated algebraic stacks are quasi-separated.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry
open Bicategory
open scoped Bicategory

universe u

namespace AlgebraicGeometry.AlgebraicStack

namespace QuasiSeparated

/-- A morphism of algebraic stacks between quasi-separated algebraic stacks is
quasi-separated. -/
instance (priority := low) of_isQuasiSeparated {S : Scheme.{u}}
    {X Y : GroupoidsOver S} [AlgebraicStack X] [AlgebraicStack Y] (f : X ⟶ Y)
    [IsQuasiSeparated X] [IsQuasiSeparated Y] : QuasiSeparated f :=
  sorry

end QuasiSeparated

namespace IsQuasiSeparated

/-- The apex of a bilimit `PseudoPullbackCone` of algebraic stacks is
quasi-separated when the three stacks are quasi-separated. -/
theorem of_isBilimit {S : Scheme.{u}} {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    {f : X ⟶ Y} {g : Z ⟶ Y}
    [IsQuasiSeparated X] [IsQuasiSeparated Y] [IsQuasiSeparated Z]
    (c : PseudoPullbackCone f g) [AlgebraicStack c.pt] (hc : c.IsBilimit) :
    IsQuasiSeparated c.pt :=
  sorry

/-- The chosen 2-fibre product of quasi-separated algebraic stacks is
quasi-separated. -/
instance (priority := low) instTwoFibreProduct {S : Scheme.{u}}
    {X Y Z : GroupoidsOver S}
    [AlgebraicStack X] [AlgebraicStack Y] [AlgebraicStack Z]
    (f : X ⟶ Y) (g : Z ⟶ Y)
    [IsQuasiSeparated X] [IsQuasiSeparated Y] [IsQuasiSeparated Z]
    [AlgebraicStack (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g)] :
    IsQuasiSeparated (TwoFibreProduct.apex.{u + 1, u, u + 1, u} f g) :=
  sorry

end IsQuasiSeparated

end AlgebraicGeometry.AlgebraicStack
