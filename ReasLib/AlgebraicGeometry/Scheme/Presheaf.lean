/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Scheme

@[expose] public section

universe u

namespace AlgebraicGeometry.Scheme

/-- Contravariant set-valued functors on schemes. -/
abbrev Presheaf : Type (u + 1) :=
  CategoryTheory.Functor AlgebraicGeometry.Scheme.{u}ᵒᵖ (Type u)

end AlgebraicGeometry.Scheme
