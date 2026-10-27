/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Gorenstein
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Flat

/-!
# Gorenstein morphisms of algebraic spaces at a point

A morphism of algebraic spaces is Gorenstein at a point when some étale
scheme square over it has top arrow Gorenstein at a germ mapping to that
point.
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces is Gorenstein at a point `x` of
`X` if some étale scheme square over `f` has top arrow Gorenstein at a point
of `U` mapping to `x`. -/
def GorensteinAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X) : Prop :=
  ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
    (u : U.left),
    (over (@AlgebraicGeometry.Etale)).presheaf a ∧
      (over (@AlgebraicGeometry.Etale)).presheaf b ∧
        a ≫ f = ofOverMap h ≫ b ∧
          Points.map a (ofOver.pointsEquiv U u) = x ∧
            Scheme.Hom.gorensteinAt h.left u

/-- Gorensteinness at a point is the existence of an étale scheme presentation
whose top arrow is Gorenstein at a germ mapping to that point. -/
theorem gorensteinAt_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X) :
    GorensteinAt f x ↔
      ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
        (u : U.left),
        (over (@AlgebraicGeometry.Etale)).presheaf a ∧
          (over (@AlgebraicGeometry.Etale)).presheaf b ∧
            a ≫ f = ofOverMap h ≫ b ∧
              Points.map a (ofOver.pointsEquiv U u) = x ∧
                Scheme.Hom.gorensteinAt h.left u :=
  sorry

namespace GorensteinAt

/-- An étale scheme square over `f` whose top arrow is Gorenstein at a germ
mapping to `x` witnesses `GorensteinAt f x`. -/
theorem of {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {x : Points X} {U V : Over S} (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y)
    (h : U ⟶ V) (u : U.left)
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b)
    (hx : Points.map a (ofOver.pointsEquiv U u) = x)
    (hg : Scheme.Hom.gorensteinAt h.left u) :
    GorensteinAt f x :=
  sorry

/-- A morphism of algebraic spaces that is Gorenstein at a point is flat
there. -/
theorem flatAt {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {x : Points X} (hg : GorensteinAt f x) : FlatAt f x :=
  sorry

end GorensteinAt

/-- A morphism of schemes over `S`, viewed as a morphism of algebraic spaces,
is Gorenstein at the image of `u` if and only if the underlying morphism of
schemes is Gorenstein at `u`. -/
theorem gorensteinAt_ofOverMap_iff {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) (u : U.left) :
    GorensteinAt (ofOverMap h) (ofOver.pointsEquiv U u) ↔
      Scheme.Hom.gorensteinAt h.left u :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
