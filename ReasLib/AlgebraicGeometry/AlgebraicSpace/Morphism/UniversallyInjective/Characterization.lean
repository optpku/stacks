/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.Data.List.TFAE
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.UniversallyInjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Surjective
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Pullback

/-!
# Characterizations of universally injective morphisms of algebraic spaces

A morphism of algebraic spaces is universally injective iff it is injective on
field-valued points iff its relative diagonal is surjective.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace AlgebraicGeometry.AlgebraicSpace

namespace UniversallyInjective

variable {S : Scheme.{u}} {X Y : AlgebraicSpace S}

/-- For a morphism of algebraic spaces, injectivity on field-valued points,
universal injectivity, and surjectivity of the relative diagonal are equivalent. -/
theorem tfae (f : X ⟶ Y) :
    List.TFAE [injectiveOnFieldPoints f, UniversallyInjective f,
      Surjective (pullback.diagonal f)] :=
  sorry

/-- A morphism of algebraic spaces is universally injective if and only if it is
injective on field-valued points. -/
theorem iff_injectiveOnFieldPoints (f : X ⟶ Y) :
    UniversallyInjective f ↔ injectiveOnFieldPoints f :=
  sorry

/-- A morphism of algebraic spaces is universally injective if and only if its
relative diagonal is surjective. -/
theorem iff_diagonal (f : X ⟶ Y) :
    UniversallyInjective f ↔ Surjective (pullback.diagonal f) :=
  sorry

/-- The relative diagonal of a universally injective morphism of algebraic spaces
is surjective. -/
instance surjective_diagonal {f : X ⟶ Y} [UniversallyInjective f] :
    Surjective (pullback.diagonal f) :=
  sorry

end UniversallyInjective

end AlgebraicGeometry.AlgebraicSpace
