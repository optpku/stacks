/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.SmoothFiniteTypeObject

/-! # Smooth finite-type objects through residue objects -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

#check (AlgebraicGeometry.GroupoidsOver.SmoothFiniteTypeObject :
  ∀ {S : Scheme.{u}} {X : GroupoidsOver S} {k : Type u} [Field k]
    (kToS : Spec (CommRingCat.of k) ⟶ S), X.p.Fiber (Over.mk kToS) → Type (u + 1))
