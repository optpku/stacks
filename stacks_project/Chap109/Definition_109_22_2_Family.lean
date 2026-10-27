/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Stable

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

/- Stable fibres and stable morphisms of schemes. -/
#check (AlgebraicGeometry.SchemeOverField.IsStableFibre :
  ∀ {k : Type u} [Field k], SchemeOverField k → Prop)

#check (AlgebraicGeometry.IsStableFamily :
  ∀ {X S : Scheme.{u}}, (X ⟶ S) → Prop)
