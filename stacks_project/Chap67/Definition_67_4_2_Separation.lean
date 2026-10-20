/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Separation
public import stacks_project.Chap65.Definition_65_6_3_Hom

/-!
# Separation axioms for morphisms of algebraic spaces

A morphism of algebraic spaces is separated, locally separated, or quasi-separated
according as its relative diagonal is a closed immersion, an immersion, or
quasi-compact, in the representable sense of Definition 65.5.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits MorphismProperty

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- The relative diagonal of a morphism of algebraic spaces, as the pullback diagonal of the
corresponding morphism of functors of points. The binders are functor morphisms because `Hom` is
definitionally a functor morphism and pullbacks are taken in `(Over S)ᵒᵖ ⥤ Type u`. -/
noncomputable def diagonal {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (φ : F ⟶ G) :
    F ⟶ pullback φ φ :=
  pullback.diagonal φ

/-- The relative diagonal of a morphism of functors of points is the pullback diagonal. -/
theorem diagonal_def {S : Scheme.{u}} {F G : (Over S)ᵒᵖ ⥤ Type u} (φ : F ⟶ G) :
    diagonal φ = pullback.diagonal φ := rfl

end AlgebraicGeometry.AlgebraicSpace
