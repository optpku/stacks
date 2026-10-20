/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.CategoryTheory.MorphismProperty.Representable
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.AtWorstNodal
public import stacks_project.Chap65.Definition_65_6_3_Hom
public import stacks_project.Chap66.Definition_66_4_1_Points
public import stacks_project.Chap67.Remark_67_22_3_EtaleLocal
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.AtWorstNodal

/-!
# At-worst-nodal morphisms of algebraic spaces

A morphism of algebraic spaces is at-worst-nodal of relative dimension 1 when
every étale scheme square over it has at-worst-nodal top arrow, in the sense of
Stacks Definition 76.55.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

/- A morphism `f : X ⟶ Y` of algebraic spaces over `S` is at-worst-nodal of
relative dimension 1 if every commutative square with étale vertical arrows from
schemes has at-worst-nodal top arrow. -/
#check (AlgebraicGeometry.AlgebraicSpace.AtWorstNodal :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

/- Every étale scheme square over an at-worst-nodal morphism has at-worst-nodal
top arrow. -/
#check (AlgebraicGeometry.AlgebraicSpace.AtWorstNodal.of_etale :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y} [AtWorstNodal f]
      {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
      (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
      (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
      (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
      (w : a ≫ f = yoneda.map h ≫ b),
    AlgebraicGeometry.AtWorstNodal h.left)

/- A morphism of algebraic spaces is at-worst-nodal of relative dimension 1 if
and only if every commutative square with étale vertical arrows from schemes has
at-worst-nodal top arrow. -/
#check (AlgebraicGeometry.AlgebraicSpace.atWorstNodal_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    AtWorstNodal f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b → AlgebraicGeometry.AtWorstNodal h.left)

namespace AtWorstNodal

/- An étale scheme square over an at-worst-nodal morphism of algebraic spaces
has at-worst-nodal top arrow. -/
#check (AlgebraicGeometry.AlgebraicSpace.AtWorstNodal.spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [AtWorstNodal f] {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = yoneda.map h ≫ b), AlgebraicGeometry.AtWorstNodal h.left)

/- A representable morphism of algebraic spaces with the relative
at-worst-nodal property is at-worst-nodal of relative dimension 1. -/
#check (AlgebraicGeometry.AlgebraicSpace.AtWorstNodal.of_presheaf :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : (over
        (@AlgebraicGeometry.AtWorstNodal :
          MorphismProperty Scheme.{u})).presheaf f),
    AtWorstNodal f)

end AtWorstNodal

/- A morphism of schemes over `S` that is at-worst-nodal of relative dimension 1
remains at-worst-nodal as a morphism of algebraic spaces via `ofOverMap`. -/
#check (AlgebraicGeometry.AlgebraicSpace.instOfOverMap :
  ∀ {S : Scheme.{u}} {U V : Over S} (h : U ⟶ V)
    [AlgebraicGeometry.AtWorstNodal h.left], AtWorstNodal (ofOverMap h))

/- A morphism of algebraic spaces is at-worst-nodal of relative dimension 1 if
and only if it has the étale-local lift of scheme-level at-worst-nodality. -/
#check (AlgebraicGeometry.AlgebraicSpace.atWorstNodal_iff_etaleLocal :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    AtWorstNodal f ↔
      etaleLocal
        (@AlgebraicGeometry.AtWorstNodal : MorphismProperty Scheme.{u}) f)

end AlgebraicGeometry.AlgebraicSpace
