/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Gorenstein

/-!
# Gorenstein morphisms of algebraic spaces at a point

The pointwise Gorenstein predicate and its scheme-presentation API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check
  (AlgebraicGeometry.AlgebraicSpace.GorensteinAt :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (x : Points X),
    Prop)

#check
  (AlgebraicGeometry.AlgebraicSpace.gorensteinAt_iff :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) (x : Points X),
    GorensteinAt f x ↔
      ∃ (U V : Over S) (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y) (h : U ⟶ V)
        (u : U.left),
        (over (@AlgebraicGeometry.Etale)).presheaf a ∧
          (over (@AlgebraicGeometry.Etale)).presheaf b ∧
            a ≫ f = ofOverMap h ≫ b ∧
              Points.map a (ofOver.pointsEquiv U u) = x ∧
                Scheme.Hom.gorensteinAt h.left u)

#check
  (AlgebraicGeometry.AlgebraicSpace.GorensteinAt.of :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {x : Points X} {U V : Over S} (a : ofOver U ⟶ X) (b : ofOver V ⟶ Y)
    (h : U ⟶ V) (u : U.left)
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = ofOverMap h ≫ b)
    (hx : Points.map a (ofOver.pointsEquiv U u) = x)
    (hg : Scheme.Hom.gorensteinAt h.left u),
    GorensteinAt f x)

#check
  (AlgebraicGeometry.AlgebraicSpace.GorensteinAt.flatAt :
    ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {x : Points X} (hg : GorensteinAt f x),
    FlatAt f x)

#check
  (AlgebraicGeometry.AlgebraicSpace.gorensteinAt_ofOverMap_iff :
    ∀ {S : Scheme.{u}} {U V : Over S}
    (h : U ⟶ V) (u : U.left),
    GorensteinAt (ofOverMap h) (ofOver.pointsEquiv U u) ↔
      Scheme.Hom.gorensteinAt h.left u)

end AlgebraicGeometry.AlgebraicSpace
