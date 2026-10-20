/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Etale
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.EtaleSquare
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.AlgebraicSpace

open MorphismProperty

/-- A morphism `f : X ⟶ Y` of algebraic spaces over `S` is locally of finite
presentation if every commutative square with étale vertical arrows from schemes
has locally-of-finite-presentation top arrow. -/
class LocallyOfFinitePresentation {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) : Prop where
  /-- Every étale scheme square over `f` has locally-of-finite-presentation top
  arrow. -/
  of_etale {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
      (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
      (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
      (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
      (w : a ≫ f = yoneda.map h ≫ b) :
    AlgebraicGeometry.LocallyOfFinitePresentation h.left

/-- A morphism of algebraic spaces is locally of finite presentation if and only
if every commutative square with étale vertical arrows from schemes has
locally-of-finite-presentation top arrow. -/
theorem locallyOfFinitePresentation_iff {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) :
    LocallyOfFinitePresentation f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b →
              AlgebraicGeometry.LocallyOfFinitePresentation h.left :=
  sorry

namespace LocallyOfFinitePresentation

/-- An étale scheme square over a locally-of-finite-presentation morphism of
algebraic spaces has locally-of-finite-presentation top arrow. -/
theorem spec {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] {U V : Over S}
    (a : yoneda.obj U ⟶ X.functorOfPoints) (b : yoneda.obj V ⟶ Y.functorOfPoints)
    (h : U ⟶ V) (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = yoneda.map h ≫ b) :
    AlgebraicGeometry.LocallyOfFinitePresentation h.left :=
  sorry

/-- The identity morphism of an algebraic space is locally of finite
presentation. -/
instance id {S : Scheme.{u}} {X : AlgebraicSpace S} :
    LocallyOfFinitePresentation (𝟙 X) :=
  sorry

/-- A representable morphism of algebraic spaces with the relative
locally-of-finite-presentation property is locally of finite presentation. -/
theorem of_presheaf {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : (over
        (@AlgebraicGeometry.LocallyOfFinitePresentation :
          MorphismProperty Scheme.{u})).presheaf f) :
    LocallyOfFinitePresentation f :=
  sorry

end LocallyOfFinitePresentation

/-- An open immersion of algebraic spaces is locally of finite presentation. -/
instance locallyOfFinitePresentation_of_isOpenImmersion {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y) [IsOpenImmersion f] :
    LocallyOfFinitePresentation f :=
  sorry

/-- An étale morphism of algebraic spaces is locally of finite presentation. -/
instance locallyOfFinitePresentation_of_etale {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (f : X ⟶ Y) [Etale f] : LocallyOfFinitePresentation f :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
