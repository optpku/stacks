/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat

/-! # Flat morphisms of represented algebraic spaces -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A flat morphism of schemes over the base induces a flat morphism of algebraic spaces. -/
instance instFlat_ofOverMap {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V)
    [AlgebraicGeometry.Flat h.left] : Flat (ofOverMap h) :=
  (flat_ofOverMap_iff h).mpr inferInstance

end AlgebraicGeometry.AlgebraicSpace
