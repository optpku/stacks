/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.PseudoCoherent

@[expose] public section

open CategoryTheory

universe u

/- The scheme-morphism pseudo-coherence predicate is owned by its reusable mathematical
module. -/
#check (AlgebraicGeometry.PseudoCoherent :
  ∀ {X Y : AlgebraicGeometry.Scheme.{u}}, (X ⟶ Y) → Prop)
