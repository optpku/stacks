/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.SpecStalk

/-!
# Stalk spectra of schematic charts

A scheme `T` over `S` and a point `t` of `T` determine the object
`Spec(𝒪_{T.left, t})` of `Over S`, together with the morphism into an
algebraic space obtained by composing with a chart `ofOver T ⟶ X`.
-/

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.specStalkOver :
  ∀ {S : Scheme.{u}} (T : Over S) (t : T.left), Over S)

#check (AlgebraicGeometry.AlgebraicSpace.specStalkOver_eq :
  ∀ {S : Scheme.{u}} (T : Over S) (t : T.left),
    specStalkOver T t = Over.mk (T.left.fromSpecStalk t ≫ T.hom))

#check (AlgebraicGeometry.AlgebraicSpace.specStalkOver_left :
  ∀ {S : Scheme.{u}} (T : Over S) (t : T.left),
    (specStalkOver T t).left = Spec (T.left.presheaf.stalk t))

#check (AlgebraicGeometry.AlgebraicSpace.specStalkOverHom :
  ∀ {S : Scheme.{u}} (T : Over S) (t : T.left), specStalkOver T t ⟶ T)

#check (AlgebraicGeometry.AlgebraicSpace.specStalkOverHom_eq :
  ∀ {S : Scheme.{u}} (T : Over S) (t : T.left),
    specStalkOverHom T t = Over.homMk (T.left.fromSpecStalk t) rfl)

#check (AlgebraicGeometry.AlgebraicSpace.specStalkOverHom_left :
  ∀ {S : Scheme.{u}} (T : Over S) (t : T.left),
    (specStalkOverHom T t).left = T.left.fromSpecStalk t)

#check (AlgebraicGeometry.AlgebraicSpace.fromSpecStalk :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (ι : ofOver U ⟶ X) (u : U.left), ofOver (specStalkOver U u) ⟶ X)

#check (AlgebraicGeometry.AlgebraicSpace.fromSpecStalk_eq :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S} {U : Over S}
    (ι : ofOver U ⟶ X) (u : U.left),
    fromSpecStalk ι u = ofOverMap (specStalkOverHom U u) ≫ ι)

#check (AlgebraicGeometry.AlgebraicSpace.fromSpecStalk_comp :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {U : Over S}
    (ι : ofOver U ⟶ X) (u : U.left) (f : X ⟶ Y),
    fromSpecStalk (ι ≫ f) u = fromSpecStalk ι u ≫ f)

end AlgebraicGeometry.AlgebraicSpace
