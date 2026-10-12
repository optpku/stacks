/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Morphism.Unramified

/-!
# Unramified morphisms of algebraic spaces

A morphism of algebraic spaces is unramified when every étale scheme square
over it has unramified top arrow, in the sense of Stacks Definition 67.38.1.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry MorphismProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace

#check (AlgebraicGeometry.AlgebraicSpace.Unramified :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S}, (X ⟶ Y) → Prop)

#check (AlgebraicGeometry.AlgebraicSpace.unramified_iff :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y),
    Unramified f ↔
      ∀ {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
        (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V),
        (over (@AlgebraicGeometry.Etale)).presheaf a →
          (over (@AlgebraicGeometry.Etale)).presheaf b →
            a ≫ f = yoneda.map h ≫ b → AlgebraicGeometry.Unramified h.left)

#check (AlgebraicGeometry.AlgebraicSpace.Unramified.spec :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    [Unramified f] {U V : Over S} (a : yoneda.obj U ⟶ X.functorOfPoints)
    (b : yoneda.obj V ⟶ Y.functorOfPoints) (h : U ⟶ V)
    (ha : (over (@AlgebraicGeometry.Etale)).presheaf a)
    (hb : (over (@AlgebraicGeometry.Etale)).presheaf b)
    (w : a ≫ f = yoneda.map h ≫ b), AlgebraicGeometry.Unramified h.left)

#check (AlgebraicGeometry.AlgebraicSpace.Unramified.id :
  ∀ {S : Scheme.{u}} {X : AlgebraicSpace S}, Unramified (𝟙 X))

#check (AlgebraicGeometry.AlgebraicSpace.Unramified.of_presheaf :
  ∀ {S : Scheme.{u}} {X Y : AlgebraicSpace S} {f : X ⟶ Y}
    (hf : (over
        (@AlgebraicGeometry.Unramified :
          MorphismProperty Scheme.{u})).presheaf f),
    Unramified f)

end AlgebraicGeometry.AlgebraicSpace
