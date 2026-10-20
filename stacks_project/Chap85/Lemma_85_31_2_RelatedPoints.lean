/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.SimplicialScheme.RelatedPoints

/-! # Related points on a simplicial scheme -/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open scoped Simplicial

universe u

namespace AlgebraicGeometry

#check (AlgebraicGeometry.relatedPoints :
  {Y : SimplicialObject Scheme.{u}} → (y : Y _⦋0⦌) → Set (Y _⦋0⦌))

#check (AlgebraicGeometry.mem_relatedPoints :
  ∀ {Y : SimplicialObject Scheme.{u}} {y y' : Y _⦋0⦌},
    y' ∈ AlgebraicGeometry.relatedPoints y ↔
      ∃ y1 : Y _⦋1⦌, Y.δ (1 : Fin 2) y1 = y ∧ Y.δ (0 : Fin 2) y1 = y')

end AlgebraicGeometry
