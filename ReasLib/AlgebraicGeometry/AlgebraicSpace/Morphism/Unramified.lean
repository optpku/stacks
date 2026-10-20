/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FormallyUnramified.Immersion
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Unramified.Basic

/-!
# Unramified morphisms of algebraic spaces

A morphism of algebraic spaces is unramified when every étale scheme square
over it has unramified top arrow. Immersions of algebraic spaces are unramified.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` is unramified if every
commutative square with étale vertical arrows from schemes has unramified top
arrow. -/
class Unramified {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- Every étale scheme square over `f` has unramified top arrow. -/
  of_etale {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
      (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
      (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
      (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
      (w : a ≫ f = yoneda.map h ≫ b) :
    AlgebraicGeometry.Unramified h.left

/-- A morphism of algebraic spaces is unramified if and only if every commutative
square with étale vertical arrows from schemes has unramified top arrow. -/
theorem unramified_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Unramified f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b → AlgebraicGeometry.Unramified h.left :=
  sorry

namespace Unramified

/-- An étale scheme square over an unramified morphism of algebraic spaces has
unramified top arrow. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Unramified f] {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = yoneda.map h ≫ b) : AlgebraicGeometry.Unramified h.left :=
  sorry

/-- The identity morphism of an algebraic space is unramified. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : Unramified (𝟙 X) :=
  sorry

/-- A representable morphism of algebraic spaces with the relative unramified
property is unramified. -/
theorem of_presheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : (over
        (@AlgebraicGeometry.Unramified :
          MorphismProperty Scheme.{u})).presheaf f) :
    Unramified f :=
  sorry

end Unramified

/-- An immersion of algebraic spaces is unramified. -/
instance unramified_of_isImmersion {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [IsImmersion f] : Unramified f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
