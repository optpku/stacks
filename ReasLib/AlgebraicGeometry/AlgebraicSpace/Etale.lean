/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.FunctorOfPoints

/-!
# Étale morphisms of algebraic spaces

A morphism of algebraic spaces is étale when postcomposition preserves étale morphisms
from schemes.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` is étale if for every étale morphism
`φ` from a scheme to `X`, the composite `φ ≫ f` is étale as a morphism from a scheme to an
algebraic space. -/
@[mk_iff]
class Etale {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- Postcomposition with `f` preserves étale morphisms from schemes. -/
  of_etale {U : Over S} (φ : yoneda.obj U ⟶ X.functorOfPoints)
    (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ) :
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf (φ ≫ f)

namespace Etale

/-- An isomorphism of algebraic spaces over `S` is étale. -/
instance of_isIso {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsIso f] :
    Etale f :=
  sorry


/-- The identity morphism of an algebraic space is étale. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Etale (𝟙 X) := sorry

/-- The composition of étale morphisms of algebraic spaces is étale. -/
instance etale_comp {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {Z : AlgebraicSpace S} (g : Y ⟶ Z) [Etale f] [Etale g] : Etale (f ≫ g) := sorry

/-- An étale morphism of algebraic spaces remains étale after precomposition with an étale
morphism from a scheme. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) [Etale f]
    {U : Over S} (φ : yoneda.obj U ⟶ X.functorOfPoints)
    (hφ : (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ) :
    (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf (φ ≫ f) := sorry

/-- A morphism of algebraic spaces is étale if postcomposition preserves étale morphisms from
schemes. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (h : ∀ {U : Over S} (φ : yoneda.obj U ⟶ X.functorOfPoints),
      (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ →
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf (φ ≫ f)) :
    Etale f := sorry

/-- A morphism of algebraic spaces is étale iff postcomposition preserves étale morphisms from
schemes, viewed as algebraic spaces via `ofOver`. -/
theorem etale_iff_ofOver {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Etale f ↔
      ∀ {U : Over S} (φ : ofOver U ⟶ X),
        (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf φ →
          (MorphismProperty.over (@AlgebraicGeometry.Etale)).presheaf (φ ≫ f) := sorry

/-- Étale morphisms of algebraic spaces over `S` are stable under composition. -/
instance instIsStableUnderComposition {S : Scheme.{u}} :
    MorphismProperty.IsStableUnderComposition
      (@Etale S : MorphismProperty (AlgebraicSpace S)) := sorry

end Etale

end AlgebraicGeometry.AlgebraicSpace
