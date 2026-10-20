/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallySmooth

@[expose] public section

open CategoryTheory

universe u

/- Scheme-level formal smoothness is the property that every induced map on compatible
affine coordinate rings is formally smooth. -/
#check (AlgebraicGeometry.FormallySmooth :
  {X Y : AlgebraicGeometry.Scheme.{u}} → (X ⟶ Y) → Prop)
