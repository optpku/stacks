/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.LocallyOfFinitePresentation
public import stacks_project.Chap65.Definition_65_6_3_Hom

/-!
# Locally of finite presentation for morphisms of algebraic spaces

A morphism of algebraic spaces is locally of finite presentation when every
étale scheme square over it has locally-of-finite-presentation top arrow, in the
sense of Stacks Definition 67.28.1 (1).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.locallyOfFinitePresentation_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    LocallyOfFinitePresentation f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b →
              AlgebraicGeometry.LocallyOfFinitePresentation h.left)

#check (AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation.spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] {U V : Over S}
    (a : yoneda.obj U ⟶ X.functorOfPoints) (b : yoneda.obj V ⟶ Y.functorOfPoints)
    (h : U ⟶ V), (over (@AlgebraicGeometry.Etale)).presheaf a →
      (over (@AlgebraicGeometry.Etale)).presheaf b →
        a ≫ f = yoneda.map h ≫ b →
          AlgebraicGeometry.LocallyOfFinitePresentation h.left)

#check (AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation.id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, LocallyOfFinitePresentation (𝟙 X))

#check (AlgebraicGeometry.AlgebraicSpace.LocallyOfFinitePresentation.of_presheaf :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y},
    (over
      (@AlgebraicGeometry.LocallyOfFinitePresentation :
        MorphismProperty Scheme.{u})).presheaf f →
      LocallyOfFinitePresentation f)

end AlgebraicGeometry.AlgebraicSpace
