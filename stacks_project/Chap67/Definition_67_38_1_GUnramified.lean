/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.GUnramified

/-!
# G-unramified morphisms and their pointwise predicates

The global and pointwise G-unramified predicates and their companion API.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.GUnramified :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.gUnramified_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    GUnramified f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b → AlgebraicGeometry.GUnramified h.left)

#check (AlgebraicGeometry.AlgebraicSpace.GUnramified.spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [GUnramified f] {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = yoneda.map h ≫ b), AlgebraicGeometry.GUnramified h.left)

#check (AlgebraicGeometry.AlgebraicSpace.GUnramified.id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, GUnramified (𝟙 X))

#check (AlgebraicGeometry.AlgebraicSpace.GUnramified.of_presheaf :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y},
    (over (@AlgebraicGeometry.GUnramified : MorphismProperty Scheme.{u})).presheaf f →
      GUnramified f)

#check (AlgebraicGeometry.AlgebraicSpace.unramified_of_gUnramified :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [GUnramified f], Unramified f)

#check (AlgebraicGeometry.AlgebraicSpace.GUnramifiedAt :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X), Prop)

#check (AlgebraicGeometry.AlgebraicSpace.gUnramifiedAt_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) (x : Points X),
    GUnramifiedAt f x ↔
      ∃ (X' : AlgebraicSpace S) (i : X' ⟶ X),
        IsOpenImmersion i ∧ x ∈ Set.range (Points.map i) ∧ GUnramified (i ≫ f))

#check (AlgebraicGeometry.AlgebraicSpace.GUnramifiedAt.of :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    {x : Points X} {X' : AlgebraicSpace S} {i : X' ⟶ X}
    [IsOpenImmersion i] (hx : x ∈ Set.range (Points.map i))
    [GUnramified (i ≫ f)], GUnramifiedAt f x)

#check (AlgebraicGeometry.AlgebraicSpace.gUnramifiedAt_of_gUnramified :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [GUnramified f] (x : Points X), GUnramifiedAt f x)

end AlgebraicGeometry.AlgebraicSpace
