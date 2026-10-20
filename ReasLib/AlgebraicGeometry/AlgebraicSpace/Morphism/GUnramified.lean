/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Points

/-!
# G-unramified morphisms of algebraic spaces

A morphism of algebraic spaces is G-unramified when every étale scheme square
over it has G-unramified top arrow. Pointwise G-unramifiedness is
G-unramifiedness after restriction to an open subspace neighbourhood.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` is G-unramified if
every commutative square with étale vertical arrows from schemes has
G-unramified top arrow. -/
class GUnramified {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) : Prop where
  /-- Every étale scheme square over `f` has G-unramified top arrow. -/
  of_etale {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
      (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
      (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
      (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
      (w : a ≫ f = yoneda.map h ≫ b) :
    AlgebraicGeometry.GUnramified h.left

/-- A morphism of algebraic spaces is G-unramified if and only if every
commutative square with étale vertical arrows from schemes has G-unramified
top arrow. -/
theorem gUnramified_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    GUnramified f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b → AlgebraicGeometry.GUnramified h.left :=
  sorry

namespace GUnramified

/-- An étale scheme square over a G-unramified morphism of algebraic spaces has
G-unramified top arrow. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [GUnramified f] {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = yoneda.map h ≫ b) : AlgebraicGeometry.GUnramified h.left :=
  sorry

/-- The identity morphism of an algebraic space is G-unramified. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} : GUnramified (𝟙 X) :=
  sorry

/-- A representable morphism of algebraic spaces with the relative G-unramified
property is G-unramified. -/
theorem of_presheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : (over
        (@AlgebraicGeometry.GUnramified :
          MorphismProperty Scheme.{u})).presheaf f) :
    GUnramified f :=
  sorry

end GUnramified

/-- A G-unramified morphism of algebraic spaces is unramified. -/
instance unramified_of_gUnramified {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [GUnramified f] : Unramified f :=
  sorry

/-- A morphism `f : X ⟶ Y` of algebraic spaces is G-unramified at a point `x`
of `X` if it is G-unramified after restriction to some open subspace
neighbourhood of `x`. -/
def GUnramifiedAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
    IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ GUnramified (i ≫ f)

/-- G-unramifiedness at a point is the existence of an open subspace
neighbourhood on which the morphism is G-unramified. -/
theorem gUnramifiedAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    GUnramifiedAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ GUnramified (i ≫ f) :=
  sorry

namespace GUnramifiedAt

/-- An open immersion `i : X' ⟶ X` whose composite `i ≫ f` is G-unramified
witnesses that `f` is G-unramified at every point of the image of `|X'|`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {x : Points X} {X' : AlgebraicSpace S} {i : X' ⟶ X}
    [IsOpenImmersion i] (hx : x ∈ Set.range (Points.map i))
    [GUnramified (i ≫ f)] : GUnramifiedAt f x :=
  sorry

end GUnramifiedAt

/-- A G-unramified morphism of algebraic spaces is G-unramified at every point
of its source. -/
theorem gUnramifiedAt_of_gUnramified {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [GUnramified f] (x : Points X) : GUnramifiedAt f x :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
