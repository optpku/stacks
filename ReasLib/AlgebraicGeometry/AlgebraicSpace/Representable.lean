/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-!
# Morphisms of presheaves representable by algebraic spaces

A morphism of presheaves on schemes over `S` is representable by algebraic spaces when
every base change along a Yoneda section from a scheme over `S` is an algebraic space.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Limits

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism of presheaves on schemes over `S` is representable by algebraic spaces
when every fibre product along a Yoneda section from a scheme over `S` is an algebraic
space. -/
def representableByAlgebraicSpaces {S : Scheme.{u}} :
    MorphismProperty ((Over S)ᵒᵖ ⥤ Type u) :=
  fun _ G a ↦ ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ G), IsAlgebraicSpace (pullback ξ a)

/-- A morphism of presheaves is representable by algebraic spaces if and only if every
fibre product along a Yoneda section from a scheme over `S` is an algebraic space. -/
theorem representableByAlgebraicSpaces_iff {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) :
    representableByAlgebraicSpaces a ↔
      ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ G), IsAlgebraicSpace (pullback ξ a) := sorry

/-- The fibre product of a representable-by-algebraic-spaces morphism along a Yoneda
section is an algebraic space. -/
theorem representableByAlgebraicSpaces.isAlgebraicSpace_pullback {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G} (ha : representableByAlgebraicSpaces a)
    {U : Over S} (ξ : yoneda.obj U ⟶ G) :
    IsAlgebraicSpace (pullback ξ a) := sorry

/-- A morphism of presheaves is representable by algebraic spaces as soon as every fibre
product along a Yoneda section is an algebraic space. -/
theorem representableByAlgebraicSpaces.of_isAlgebraicSpace_pullback {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G}
    (h : ∀ ⦃U : Over S⦄ (ξ : yoneda.obj U ⟶ G), IsAlgebraicSpace (pullback ξ a)) :
    representableByAlgebraicSpaces a := sorry

/-- The fibre product of a representable-by-algebraic-spaces morphism along a Yoneda
section is the functor of points of an algebraic space over `S`. -/
theorem representableByAlgebraicSpaces.exists_algebraicSpace {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} {a : F ⟶ G} (ha : representableByAlgebraicSpaces a)
    {U : Over S} (ξ : yoneda.obj U ⟶ G) :
    ∃ X : AlgebraicSpace S, X.functorOfPoints = pullback ξ a := sorry

namespace representableByAlgebraicSpaces

/-- The property of being representable by algebraic spaces is stable under base change. -/
theorem isStableUnderBaseChange {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderBaseChange (@representableByAlgebraicSpaces S) := sorry

attribute [instance] isStableUnderBaseChange

end representableByAlgebraicSpaces

/-- Every morphism between algebraic spaces over a scheme is representable by algebraic spaces. -/
theorem representableByAlgebraicSpaces.of_hom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : representableByAlgebraicSpaces f := sorry

/-- The pullback of a morphism between algebraic spaces along a scheme-valued point is an algebraic space. -/
def instIsAlgebraicSpace_pullback_hom {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) {U : Over S} (ξ : yoneda.obj U ⟶ Y.functorOfPoints) :
    IsAlgebraicSpace (pullback ξ f) :=
  representableByAlgebraicSpaces.of_hom f ξ

/-- A presheaf admitting a morphism representable by algebraic spaces to an algebraic
space is itself an algebraic space. -/
theorem IsAlgebraicSpace.of_representableByAlgebraicSpaces {S : Scheme.{u}}
    {F G : (Over S)ᵒᵖ ⥤ Type u} (a : F ⟶ G) [IsAlgebraicSpace G]
    (ha : representableByAlgebraicSpaces a) : IsAlgebraicSpace F :=
  sorry

/-- The fibre product of a morphism representable by algebraic spaces along a map
from an algebraic-space presheaf is an algebraic space. -/
theorem IsAlgebraicSpace.pullback {S : Scheme.{u}} {F G X : (Over S)ᵒᵖ ⥤ Type u}
    (a : F ⟶ G) (ha : representableByAlgebraicSpaces a) [IsAlgebraicSpace X]
    (f : X ⟶ G) : IsAlgebraicSpace (pullback f a) :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
