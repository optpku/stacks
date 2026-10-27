/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Gorenstein.Global
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.CohenMacaulay

/-! # Gorenstein morphisms of algebraic spaces are Cohen–Macaulay -/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Gorenstein

/-- A Gorenstein morphism of algebraic spaces is Cohen–Macaulay. -/
instance instCohenMacaulay {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Gorenstein f] : CohenMacaulay f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace.Gorenstein
