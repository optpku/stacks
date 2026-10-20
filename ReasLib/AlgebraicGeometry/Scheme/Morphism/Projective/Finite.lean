/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Projective.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Finite morphisms are projective

This file relates finite morphisms of schemes to projective morphisms.
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- Every finite morphism of schemes is projective. -/
theorem IsFinite.projective {X S : Scheme.{u}} {f : X ⟶ S} (hf : IsFinite f) :
    Projective f := sorry

/-- A finite morphism of schemes carries the canonical projective-morphism property. -/
instance instProjectiveOfIsFinite {X S : Scheme.{u}} (f : X ⟶ S) [IsFinite f] :
    Projective f := IsFinite.projective inferInstance

end AlgebraicGeometry
