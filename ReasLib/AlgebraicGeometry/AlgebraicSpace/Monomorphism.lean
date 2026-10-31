/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.Data.List.TFAE
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback
public import ReasLib.CategoryTheory.Presheaf.MonoEpi

@[expose] public section

open CategoryTheory AlgebraicGeometry CategoryTheory.MorphismProperty Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of algebraic spaces over a scheme is a monomorphism exactly when every
component of its functor-of-points transformation is injective. -/
theorem mono_iff_injective {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Mono f ↔ ∀ (T : (Over S)ᵒᵖ), Function.Injective (f.app T) := sorry

/-- For a morphism of algebraic spaces, componentwise injectivity, categorical
monicity, and invertibility of the relative diagonal are equivalent. -/
theorem mono_tfae {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    List.TFAE [∀ (T : (Over S)ᵒᵖ), Function.Injective (f.app T), Mono f,
      IsIso (pullback.diagonal f)] := sorry

end AlgebraicGeometry.AlgebraicSpace
