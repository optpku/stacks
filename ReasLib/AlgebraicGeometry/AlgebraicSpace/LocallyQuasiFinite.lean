/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism

/-!
# Locally quasi-finite morphisms of algebraic spaces

 A morphism of algebraic spaces is locally quasi-finite when every étale
 scheme square over it has locally quasi-finite top arrow.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` is locally quasi-finite
if every commutative square with étale vertical arrows from schemes has locally
quasi-finite top arrow. -/
class LocallyQuasiFinite {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y) :
    Prop where
  /-- Every étale scheme square over `f` has locally quasi-finite top arrow. -/
  of_etale {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
      (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
      (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
      (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
      (w : a ≫ f = yoneda.map h ≫ b) :
    AlgebraicGeometry.LocallyQuasiFinite h.left

/-- A morphism of algebraic spaces is locally quasi-finite if and only if every
commutative square with étale vertical arrows from schemes has locally
quasi-finite top arrow. -/
theorem locallyQuasiFinite_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    LocallyQuasiFinite f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b →
              AlgebraicGeometry.LocallyQuasiFinite h.left :=
  sorry

namespace LocallyQuasiFinite

/-- An étale scheme square over a locally quasi-finite morphism of algebraic
spaces has locally quasi-finite top arrow. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyQuasiFinite f] {U V : Over S}
    (a : yoneda.obj U ⟶ X.functorOfPoints) (b : yoneda.obj V ⟶ Y.functorOfPoints)
    (h : U ⟶ V) (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = yoneda.map h ≫ b) :
    AlgebraicGeometry.LocallyQuasiFinite h.left :=
  sorry

/-- The identity morphism of an algebraic space is locally quasi-finite. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    LocallyQuasiFinite (𝟙 X) :=
  sorry

/-- A representable morphism of algebraic spaces with the relative locally
quasi-finite property is locally quasi-finite. -/
theorem of_presheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : (over
        (@AlgebraicGeometry.LocallyQuasiFinite :
          MorphismProperty Scheme.{u})).presheaf f) :
    LocallyQuasiFinite f :=
  sorry

end LocallyQuasiFinite

end AlgebraicGeometry.AlgebraicSpace
