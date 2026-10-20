/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Envelope

universe u

/- The compatibility module exposes the shared envelope predicate at its complete type. -/
#check
  (AlgebraicGeometry.IsEnvelope : {Y X : AlgebraicGeometry.Scheme.{u}} → (Y ⟶ X) → Prop)
