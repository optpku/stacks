/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Factorization

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.BivariantClass

/-- A morphism of schemes over a base has a Gysin map when it factors as an immersion
followed by a smooth morphism. -/
def HasGysinMap {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) : Prop :=
  MorphismProperty.comp
    (MorphismProperty.inverseImage (@IsImmersion : MorphismProperty Scheme.{u}) (Over.forget S))
    (MorphismProperty.inverseImage (@Smooth : MorphismProperty Scheme.{u}) (Over.forget S)) f

namespace HasGysinMap

/-- A morphism has a Gysin map exactly when it admits explicit factorization data consisting
of an immersion followed by a smooth morphism. -/
theorem iff_exists {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    HasGysinMap f ↔
      ∃ (middle : Over S) (i : X ⟶ middle) (g : middle ⟶ Y),
        IsImmersion i.left ∧ Smooth g.left ∧ i ≫ g = f := sorry

end HasGysinMap

end AlgebraicGeometry.BivariantClass
