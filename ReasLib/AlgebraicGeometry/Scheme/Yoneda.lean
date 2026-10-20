/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Basic
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.MorphismProperty.Representable

@[expose] public section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry

/-- The Yoneda map induced by a morphism of schemes over a base is relatively
representable. -/
theorem yonedaMap_relativelyRepresentable {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) :
    yoneda.relativelyRepresentable (yoneda.map f) :=
  CategoryTheory.Functor.relativelyRepresentable.map yoneda f

end AlgebraicGeometry
